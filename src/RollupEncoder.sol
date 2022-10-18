// SPDX-License-Identifier: Apache-2.0
// Copyright 2022 Aztec.
pragma solidity >=0.8.4;

import {Script, Vm} from "forge-std/Script.sol";
import {ISubsidy} from "./aztec/interfaces/ISubsidy.sol";
import {IRollupProcessorV2} from "./aztec/interfaces/IRollupProcessorV2.sol";
import {AztecTypes} from "./aztec/libraries/AztecTypes.sol";
import {RollupProcessorLibrary} from "./aztec/libraries/RollupProcessorLibrary.sol";

interface Helper {
    function defiInteractionHashes(uint256) external view returns (bytes32);
}

/**
 * @notice A contract which allows testing bridges against live RollupProcessor deployment.
 * @author Lasse Herskind, Jan Benes
 * @dev Inheriting from Script in order to have access to `vm`
 */
contract RollupEncoder is Script {
    /* solhint-enable error-name-mixedcase */
    error UnsupportedAsset(address);

    // error lib errors
    error InvalidCaller();
    error InputAssetAAndOutputAssetAIsEth();
    error InputAssetANotERC20OrEth();
    error OutputAssetANotERC20OrEth();
    error InputAssetBNotEmpty();
    error OutputAssetBNotEmpty();
    error InputAssetInvalid();
    error OutputAssetInvalid();
    error InputAssetNotEqZkAToken();
    error InvalidAToken();
    error ZkTokenAlreadyExists();
    error ZkTokenDontExist();
    error ZeroValue();
    error AsyncDisabled();

    /*----------------------------------------
    EVENTS
    ----------------------------------------*/
    event OffchainData(uint256 indexed rollupId, uint256 chunk, uint256 totalChunks, address sender);
    event RollupProcessed(uint256 indexed rollupId, bytes32[] nextExpectedDefiHashes, address sender);
    event DefiBridgeProcessed(
        uint256 indexed encodedBridgeCallData,
        uint256 indexed nonce,
        uint256 totalInputValue,
        uint256 totalOutputValueA,
        uint256 totalOutputValueB,
        bool result,
        bytes errorReason
    );
    event AsyncDefiBridgeProcessed(
        uint256 indexed encodedBridgeCallData, uint256 indexed nonce, uint256 totalInputValue
    );
    event Deposit(uint256 indexed assetId, address indexed depositorAddress, uint256 depositValue);
    event WithdrawError(bytes errorReason);
    event AssetAdded(uint256 indexed assetId, address indexed assetAddress, uint256 assetGasLimit);
    event BridgeAdded(uint256 indexed bridgeAddressId, address indexed bridgeAddress, uint256 bridgeGasLimit);
    event RollupProviderUpdated(address indexed providerAddress, bool valid);
    event VerifierUpdated(address indexed verifierAddress);
    event Paused(address account);
    event Unpaused(address account);
    event DelayBeforeEscapeHatchUpdated(uint32 delay);
    event AssetCapUpdated(uint256 assetId, uint256 pendingCap, uint256 dailyCap);
    event CappedUpdated(bool isCapped);

    enum ProofId {
        PADDING,
        DEPOSIT,
        WITHDRAW,
        SEND,
        ACCOUNT,
        DEFI_DEPOSIT,
        DEFI_CLAIM
    }

    struct OffchainDataStruct {
        bytes32 viewing1;
        bytes32 viewing2;
    }

    struct DepositStruct {
        uint256 assetId;
        uint256 amount;
        uint256 fee; // Just assume it is the same asset
        uint256 privKey;
        bytes32 digest;
    }

    struct WithdrawStruct {
        uint256 assetId;
        uint256 amount;
        address publicOwner;
    }

    struct DefiInteractionStruct {
        uint256 bridgeCallData;
        uint256 inputValue;
    }

    struct DefiBridgeProcessedStruct {
        uint256 encodedBridgeCallData;
        uint256 nonce;
        uint256 totalInputValue;
        uint256 totalOutputValueA;
        uint256 totalOutputValueB;
        bool result;
        bytes errorReason;
    }

    // Note: Called NUMBER_OF_ASSETS in Decoder - calling it differently here to avoid collisions in tests which
    //       inherit from Decoder.
    uint256 internal constant MAX_ASSETS_IN_BLOCK = 16;

    uint256 private constant INPUT_ASSET_ID_A_SHIFT = 32;
    uint256 private constant INPUT_ASSET_ID_B_SHIFT = 62;
    uint256 private constant OUTPUT_ASSET_ID_A_SHIFT = 92;
    uint256 private constant OUTPUT_ASSET_ID_B_SHIFT = 122;
    uint256 private constant BITCONFIG_SHIFT = 152;
    uint256 private constant AUX_DATA_SHIFT = 184;
    uint256 internal constant VIRTUAL_ASSET_ID_FLAG_SHIFT = 29;
    uint256 internal constant VIRTUAL_ASSET_ID_FLAG = 0x20000000; // 2 ** 29
    uint256 private constant MASK_THIRTY_TWO_BITS = 0xffffffff;
    uint256 private constant MASK_THIRTY_BITS = 0x3fffffff;
    uint256 private constant MASK_SIXTY_FOUR_BITS = 0xffffffffffffffff;

    bytes32 private constant DATA_ROOT = 0x18ceb5cd201e1cee669a5c3ad96d3c4e933a365b37046fc3178264bede32c68d;
    bytes32 private constant NULL_ROOT = 0x298329c7d0936453f354e4a5eef4897296cc0bf5a66f2a528318508d2088dafa;
    bytes32 private constant DATA_ROOTS_ROOT = 0x2fd2364bfe47ccb410eba3a958be9f39a8c6aca07db1abd15f5a211f51505071;
    bytes32 private constant DEFI_ROOT = 0x2e4ab7889ab3139204945f9e722c7a8fdb84e66439d787bd066c3d896dba04ea;

    bytes32 private constant DEFI_RESULT_ZERO_HASH = 0x2d25a1e3a51eb293004c4b56abe12ed0da6bca2b4a21936752a85d102593c1b4;

    uint256 private constant CIRCUIT_MODULUS =
        21888242871839275222246405745257275088548364400416034343698204186575808495617;

    uint256 private constant TX_PUBLIC_INPUT_LENGTH = 256;

    uint256 private constant NUM_ASYNC_DEFI_INTERACTION_HASHES_MASK =
        type(uint256).max - (uint256(type(uint16).max) << 192);

    address internal constant ROLLUP_PROVIDER = payable(0xA173BDdF4953C1E8be2cA0695CFc07502Ff3B1e7);

    bytes32 public constant BRIDGE_PROCESSED_EVENT_SIG =
        keccak256("DefiBridgeProcessed(uint256,uint256,uint256,uint256,uint256,bool,bytes)");
    bytes32 public constant ASYNC_BRIDGE_PROCESSED_EVENT_SIG =
        keccak256("AsyncDefiBridgeProcessed(uint256,uint256,uint256)");

    mapping(uint256 => DepositStruct) private depositsL2;
    mapping(uint256 => WithdrawStruct) private withdrawalsL2;
    mapping(uint256 => DefiInteractionStruct) private defiInteractionsL2;
    // assetId => fee amount
    mapping(uint256 => uint256) private fees;

    uint256 public depositsL2Length;
    uint256 public withdrawalsL2Length;
    uint256 public defiInteractionLength;

    // @dev Placing `mockVerifierCall` next to `rollupBeneficiary` would cause revert in a Decoder because these 2
    //      variables would get packed to 1 slot and then the boolean value would get accidentally saved to the proof
    //      along with rollupBeneficiary (we pass there the whole storage slot during proof data construction)
    bool private mockVerifierCall = true;
    uint256 public nextRollupId = 0;
    address public rollupBeneficiary;
    IRollupProcessorV2 public rollupProcessor;

    constructor(address _rollupProcessor) {
        rollupProcessor = IRollupProcessorV2(_rollupProcessor);
    }

    /**
     * @notice A function used to construct and submit rollup batch to `rollupProcessor`
     * @dev Before calling this method deposits, withdrawals and defiInteractions should be registered through
     * `depositL2(...)`, `withdrawL2(...)`, `defiInteractionL2(...)` functions.
     */
    function processRollup() public {
        (bytes memory encodedProofData, bytes memory signatures) = _computeRollup();
        vm.prank(ROLLUP_PROVIDER);
        rollupProcessor.processRollup(encodedProofData, signatures);
        nextRollupId++;
    }

    /**
     * @notice A function used to construct and submit a failing rollup batch to `rollupProcessor`
     * @dev Before calling this method deposits, withdrawals and defiInteractions should be registered through
     * `depositL2(...)`, `withdrawL2(...)`, `defiInteractionL2(...)` functions.
     */
    function processRollupFail(bytes memory _err) public {
        (bytes memory encodedProofData, bytes memory signatures) = _computeRollup();
        vm.prank(ROLLUP_PROVIDER);
        vm.expectRevert(_err);
        rollupProcessor.processRollup(encodedProofData, signatures);
        nextRollupId++;
    }

    /**
     * @notice A function used to construct and submit a failing rollup batch to `rollupProcessor`
     * @dev Before calling this method deposits, withdrawals and defiInteractions should be registered through
     * `depositL2(...)`, `withdrawL2(...)`, `defiInteractionL2(...)` functions.
     */
    function processRollupFail(bytes4 _err) public {
        (bytes memory encodedProofData, bytes memory signatures) = _computeRollup();
        vm.prank(ROLLUP_PROVIDER);
        vm.expectRevert(_err);
        rollupProcessor.processRollup(encodedProofData, signatures);
        nextRollupId++;
    }

    /**
     * @notice A function used to construct and submit rollup batch to `rollupProcessor`
     * @return outputValueA The amount of outputAssetA returned from the DeFi bridge interaction in this rollup
     * @return outputValueB The amount of outputAssetB returned from the DeFi bridge interaction in this rollup
     * @return isAsync A flag indicating whether the DeFi bridge interaction in this rollup was async
     * @dev Before calling this method deposits, withdrawals and defiInteractions should be registered through
     * `depositL2(...)`, `withdrawL2(...)`, `defiInteractionL2(...)` functions.
     */
    function processRollupAndGetBridgeResult()
        public
        returns (uint256 outputValueA, uint256 outputValueB, bool isAsync)
    {
        (bytes memory encodedProofData, bytes memory signatures) = _computeRollup();

        vm.recordLogs();
        vm.prank(ROLLUP_PROVIDER);
        rollupProcessor.processRollup(encodedProofData, signatures);
        nextRollupId++;

        return _getDefiBridgeProcessedData();
    }

    /**
     * @notice A function used to construct and submit a rollup batch with asserts for the events emitted
     * @dev Before calling this method deposits, withdrawals and defiInteractions should be registered through
     * `depositL2(...)`, `withdrawL2(...)`, `defiInteractionL2(...)` functions.
     */
    function processRollupCheckEvents(DefiBridgeProcessedStruct[] memory _events) public {
        (bytes memory encodedProofData, bytes memory signatures) = _computeRollup();

        for (uint256 i = 0; i < _events.length; i++) {
            DefiBridgeProcessedStruct memory temp = _events[i];
            vm.expectEmit(true, true, false, true);
            emit DefiBridgeProcessed(
                temp.encodedBridgeCallData,
                temp.nonce,
                temp.totalInputValue,
                temp.totalOutputValueA,
                temp.totalOutputValueB,
                temp.result,
                temp.errorReason
                );
        }

        vm.prank(ROLLUP_PROVIDER);
        rollupProcessor.processRollup(encodedProofData, signatures);
        nextRollupId++;
    }

    /**
     * @notice A function used to register an L2 deposit to be processed in the next rollup
     * @param _assetId Id of the deposited asset
     * @param _amount Amount of the deposited asset
     * @param _fee Fee to be taken by Falafel for processing the deposit
     * @param _privKey Private key corresponding to the deposit owner
     * @dev This is a claim on L2 on funds deposited on L1
     * @dev Note: For deposits to pass the corresponsing deposit has to be in `rollupProcessor.userPendingDeposits`.
     */
    function depositL2(uint256 _assetId, uint256 _amount, uint256 _fee, uint256 _privKey) public {
        depositsL2[depositsL2Length++] =
            DepositStruct({assetId: _assetId, amount: _amount, fee: _fee, privKey: _privKey, digest: bytes32("")});

        if (_fee > 0) {
            require(
                _assetId < MAX_ASSETS_IN_BLOCK, "Functionality handling assetId >= MAX_ASSETS_IN_BLOCK not implemented"
            );
            fees[_assetId] += _fee;
        }
    }

    function depositL2(uint256 _assetId, uint256 _amount, uint256 _fee, uint256 _privKey, bytes32 _proofHash) public {
        depositsL2[depositsL2Length++] =
            DepositStruct({assetId: _assetId, amount: _amount, fee: _fee, privKey: _privKey, digest: _proofHash});
        if (_fee > 0) {
            require(
                _assetId < MAX_ASSETS_IN_BLOCK, "Functionality handling assetId >= MAX_ASSETS_IN_BLOCK not implemented"
            );
            fees[_assetId] += _fee;
        }
    }

    /**
     * @notice A function used to register a withdrawal from L2 to be processed in the next rollup.
     * @param _assetId Id of the deposited asset
     * @param _amount Amount of the deposited asset
     * @param _owner Address on L1 which will receive the withdrawn funds once the rollup is processed
     */
    function withdrawL2(uint256 _assetId, uint256 _amount, address _owner) public {
        withdrawalsL2[withdrawalsL2Length++] = WithdrawStruct({assetId: _assetId, amount: _amount, publicOwner: _owner});
    }

    /**
     * @notice A function used to register a defi interaction to be processed in the next rollup.
     * @param _bridgeAddressId Id of the bridge address
     * @param _inputAssetA A struct detailing the first input asset
     * @param _inputAssetB A struct detailing the second input asset
     * @param _outputAssetA A struct detailing the first output asset
     * @param _outputAssetB A struct detailing the second output asset
     * @param _auxData Bridge specific data to be passed into the bridge contract (e.g. slippage, nftID etc.)
     * @param _totalInputValue An amount of input assets transferred to the bridge
     * @return The encodedBridgeCallData for the given interaction
     */
    function defiInteractionL2(
        uint256 _bridgeAddressId,
        AztecTypes.AztecAsset memory _inputAssetA,
        AztecTypes.AztecAsset memory _inputAssetB,
        AztecTypes.AztecAsset memory _outputAssetA,
        AztecTypes.AztecAsset memory _outputAssetB,
        uint64 _auxData,
        uint256 _totalInputValue
    ) public returns (uint256) {
        uint256 encodedBridgeCallData =
            encodeBridgeCallData(_bridgeAddressId, _inputAssetA, _inputAssetB, _outputAssetA, _outputAssetB, _auxData);
        defiInteractionsL2[defiInteractionLength++] =
            DefiInteractionStruct({bridgeCallData: encodedBridgeCallData, inputValue: _totalInputValue});
        return encodedBridgeCallData;
    }

    /**
     * @notice A function used to register a defi interaction to be processed in the next rollup.
     * @param _encodedBridgeCallData The encodedBridgeCallData for the given interaction
     * @param _totalInputValue An amount of input assets transferred to the bridge
     */
    function defiInteractionL2(uint256 _encodedBridgeCallData, uint256 _totalInputValue) public {
        defiInteractionsL2[defiInteractionLength++] =
            DefiInteractionStruct({bridgeCallData: _encodedBridgeCallData, inputValue: _totalInputValue});
    }

    /**
     * @notice Sets `rollupBeneficiary` storage variable
     * @param _rollupBeneficiary An address which receives rollup block's fee
     */
    function setRollupBeneficiary(address _rollupBeneficiary) public {
        rollupBeneficiary = _rollupBeneficiary;
    }

    /**
     * @notice Sets `mockVerifierCall` storage variable
     * @param _mockVerifierCall A flag specifying whether a call to verifier should be mocked
     * @dev Used in NoCode.t.sol
     */
    function setMockVerifierCall(bool _mockVerifierCall) public {
        mockVerifierCall = _mockVerifierCall;
    }

    /**
     * @notice Helper function to get an `AztecAsset` object for the supported real `_asset`
     * @dev if `_asset` is not supported will revert with `UnsupportedAsset(_asset)`.
     * @dev Virtual assets are not supported by the function
     * @param _asset The address of the asset to fetch
     * @return A populated supported `AztecAsset`
     */
    function getRealAztecAsset(address _asset) public view returns (AztecTypes.AztecAsset memory) {
        if (_asset == address(0)) {
            return AztecTypes.AztecAsset({id: 0, erc20Address: address(0), assetType: AztecTypes.AztecAssetType.ETH});
        } else {
            return AztecTypes.AztecAsset({
                id: getAssetId(_asset),
                erc20Address: _asset,
                assetType: AztecTypes.AztecAssetType.ERC20
            });
        }
    }

    /**
     * @notice Helper function to get the id a given `_asset`
     * @dev if `_asset` is not supported will revert with `UnsupportedAsset(_asset)`
     * @param _asset The address of the asset to fetch id for
     * @return The id matching `_asset`
     */
    function getAssetId(address _asset) public view returns (uint256) {
        if (_asset == address(0)) {
            return 0;
        }
        uint256 length = rollupProcessor.getSupportedAssetsLength();
        for (uint256 i = 1; i <= length; i++) {
            address fetched = rollupProcessor.getSupportedAsset(i);
            if (fetched == _asset) {
                return i;
            }
        }
        revert UnsupportedAsset(_asset);
    }

    /**
     * @notice Helper function to encode bridge call data into a bit-string
     * @dev For more info see the rollup implementation at "rollup.aztec.eth" that decodes
     * @param _bridgeAddressId id of the specific bridge (index in supportedBridge + 1)
     * @param _inputAssetA The first input asset
     * @param _inputAssetB The second input asset
     * @param _outputAssetA The first output asset
     * @param _outputAssetB The second output asset
     * @param _auxData Auxiliary data that is passed to the bridge
     * @return encodedBridgeCallData - The encoded bitmap containing encoded information about the call
     */
    function encodeBridgeCallData(
        uint256 _bridgeAddressId,
        AztecTypes.AztecAsset memory _inputAssetA,
        AztecTypes.AztecAsset memory _inputAssetB,
        AztecTypes.AztecAsset memory _outputAssetA,
        AztecTypes.AztecAsset memory _outputAssetB,
        uint256 _auxData
    ) public pure returns (uint256 encodedBridgeCallData) {
        encodedBridgeCallData = _bridgeAddressId & MASK_THIRTY_TWO_BITS;

        // Input assets
        encodedBridgeCallData = encodedBridgeCallData | (_encodeAsset(_inputAssetA) << INPUT_ASSET_ID_A_SHIFT);
        encodedBridgeCallData = encodedBridgeCallData | (_encodeAsset(_inputAssetB) << INPUT_ASSET_ID_B_SHIFT);
        encodedBridgeCallData = encodedBridgeCallData | (_encodeAsset(_outputAssetA) << OUTPUT_ASSET_ID_A_SHIFT);
        encodedBridgeCallData = encodedBridgeCallData | (_encodeAsset(_outputAssetB) << OUTPUT_ASSET_ID_B_SHIFT);

        // Aux data
        encodedBridgeCallData = encodedBridgeCallData | ((_auxData & MASK_SIXTY_FOUR_BITS) << AUX_DATA_SHIFT);

        // bitconfig
        uint256 bitConfig = (_inputAssetB.assetType != AztecTypes.AztecAssetType.NOT_USED ? 1 : 0)
            | (_outputAssetB.assetType != AztecTypes.AztecAssetType.NOT_USED ? 2 : 0);
        encodedBridgeCallData = encodedBridgeCallData | (bitConfig << BITCONFIG_SHIFT);
    }

    /**
     * @notice A helper function used to compute defiInteractionHash
     * @param _encodedBridgeCallData The encodedBridgeCallData of the given interaction
     * @param _interactionNonce Nonce of the interaction
     * @param _totalInputValue An amount of input assets transferred to the bridge
     * @param _outputValueA An amount of `_outputAssetA` returned from this interaction
     * @param _outputValueB An amount of `_outputAssetB` returned from this interaction
     * @param _success A flag indicating whether the interaction succeeded
     * @return defiInteractionHash of a given interaction
     */
    function computeDefiInteractionHash(
        uint256 _encodedBridgeCallData,
        uint256 _interactionNonce,
        uint256 _totalInputValue,
        uint256 _outputValueA,
        uint256 _outputValueB,
        bool _success
    ) public pure returns (bytes32) {
        return bytes32(
            uint256(
                sha256(
                    abi.encode(
                        _encodedBridgeCallData,
                        _interactionNonce,
                        _totalInputValue,
                        _outputValueA,
                        _outputValueB,
                        _success
                    )
                )
            ) % CIRCUIT_MODULUS
        );
    }

    function _computeRollup() internal returns (bytes memory pd, bytes memory signatures) {
        _prepRollup();

        // TODO make the size computation here precise and dynamic
        pd = new bytes(256 * 64);
        signatures = new bytes(0x20 + 0x60 * depositsL2Length);

        uint256 numRealTxs = depositsL2Length + withdrawalsL2Length + defiInteractionLength;

        {
            uint256 _nextRollupId = nextRollupId;
            uint256 numDataLeaves = numRealTxs * 2;
            uint256 dataSize = rollupProcessor.getDataSize();

            uint256 newDataStartIndex =
                (dataSize % numDataLeaves == 0) ? dataSize : (dataSize + numDataLeaves - (dataSize % numDataLeaves));

            assembly {
                mstore(add(pd, add(0x20, mul(0x20, 0))), _nextRollupId)
                // mstore(add(pd, add(0x20, mul(0x20, 1))), size)
                mstore(add(pd, add(0x20, mul(0x20, 2))), newDataStartIndex)
                mstore(add(pd, add(0x20, mul(0x20, 3))), DATA_ROOT)
                mstore(add(pd, add(0x20, mul(0x20, 4))), DATA_ROOT)
                mstore(add(pd, add(0x20, mul(0x20, 5))), NULL_ROOT)
                mstore(add(pd, add(0x20, mul(0x20, 6))), NULL_ROOT)
                mstore(add(pd, add(0x20, mul(0x20, 7))), DATA_ROOTS_ROOT)
                mstore(add(pd, add(0x20, mul(0x20, 8))), DATA_ROOTS_ROOT)
                mstore(add(pd, add(0x20, mul(0x20, 9))), DEFI_ROOT)
                mstore(add(pd, add(0x20, mul(0x20, 10))), DEFI_ROOT)
            }
        }

        // Time to loop for the bridges. Ignores any proof data related to the interaction
        for (uint256 i = 0; i < 32; i++) {
            DefiInteractionStruct storage interaction = defiInteractionsL2[i];
            if (interaction.bridgeCallData != 0) {
                uint256 bridgeCallData = interaction.bridgeCallData;
                uint256 inputValue = interaction.inputValue;
                assembly {
                    mstore(add(pd, add(0x20, mul(0x20, add(11, i)))), bridgeCallData)
                    mstore(add(pd, add(0x20, mul(0x20, add(43, i)))), inputValue)
                }
            }
        }

        // Fees
        for (uint256 assetId = 0; assetId < MAX_ASSETS_IN_BLOCK; assetId++) {
            uint256 feeAmount = fees[assetId];
            if (feeAmount > 0) {
                assembly {
                    mstore(add(pd, add(0x20, mul(0x20, add(75, assetId)))), assetId)
                    mstore(add(pd, add(0x20, mul(0x20, add(91, assetId)))), feeAmount)
                }
                delete fees[assetId];
            } else {
                assembly {
                    mstore(add(pd, add(0x20, mul(0x20, add(75, assetId)))), 0x40000000)
                }
            }
        }

        {
            // Interaction notes. For mock, ignore any proofs related to this
            uint256 defiInteractionLength_ = rollupProcessor.getDefiInteractionHashesLength();
            uint256 numPending = 32 > defiInteractionLength_ ? defiInteractionLength_ : 32;
            uint256 offset = defiInteractionLength_ - numPending;
            for (uint256 i = 0; i < 32; i++) {
                if (offset + i < defiInteractionLength_) {
                    {
                        bytes32 hash = Helper(address(rollupProcessor)).defiInteractionHashes(offset + i);
                        assembly {
                            mstore(add(pd, add(0x20, mul(0x20, add(107, i)))), hash)
                        }
                    }
                } else {
                    assembly {
                        mstore(add(pd, add(0x20, mul(0x20, add(107, i)))), DEFI_RESULT_ZERO_HASH)
                    }
                }
            }
            bytes32 prevDefiInteractionsHash;
            assembly {
                let hashData := add(pd, add(0x20, mul(0x20, 107)))
                pop(staticcall(gas(), 0x2, hashData, 1024, 0x00, 0x20))
                prevDefiInteractionsHash := mod(mload(0x00), CIRCUIT_MODULUS)
            }
            vm.store(address(rollupProcessor), bytes32(uint256(16)), prevDefiInteractionsHash);
        }

        {
            bytes32 prev = rollupProcessor.prevDefiInteractionsHash();
            address rollupBeneficiaryUnpacked = rollupBeneficiary;
            assembly {
                mstore(add(pd, add(0x20, mul(0x20, 139))), prev)
                mstore(add(pd, add(0x20, mul(0x20, 140))), rollupBeneficiaryUnpacked)
            }
        }

        // Handle deposits
        uint256 proofLoc = 0x20 + 0x11c8;
        uint256 sigIndex = 0x20;
        for (uint256 i = 0; i < defiInteractionLength; i++) {
            proofLoc = _addDefiTx(pd, proofLoc, i);
        }
        for (uint256 i = 0; i < depositsL2Length; i++) {
            (proofLoc, sigIndex) = _addDepositTx(pd, proofLoc, signatures, sigIndex, i);
        }
        for (uint256 i = 0; i < withdrawalsL2Length; i++) {
            proofLoc = _addWithdrawTx(pd, proofLoc, i);
        }

        {
            uint256 length = proofLoc - (0x20 + 0x11c8);
            assembly {
                mstore(add(pd, add(0x20, mul(0x20, 141))), numRealTxs)
                mstore(add(pd, add(0x20, mul(0x20, 1))), numRealTxs)
                let pre := mload(add(pd, add(0x20, 0x11c0)))
                let txCount := shl(224, numRealTxs)
                let encodedTxDataLength := shl(192, length)
                let after := or(pre, or(encodedTxDataLength, txCount))
                mstore(add(pd, add(0x20, 0x11c0)), after)
            }
        }

        depositsL2Length = withdrawalsL2Length = defiInteractionLength = 0;

        {
            uint256 proofSize = proofLoc - 0x20;
            uint256 sigSize = sigIndex - 0x20;
            assembly {
                mstore(pd, proofSize)
                mstore(signatures, sigSize)
            }
        }
    }

    /**
     * @notice A function which iterates through logs, decodes relevant events and returns values which were originally
     *         returned from bridge's `convert(...)` function.
     * @dev You have to call `vm.recordLogs()` before calling this function
     * @dev If there are multiple DefiBridgeProcessed events, values of the last one are returned --> this occurs when
     *      the bridge finalises interactions within it's convert functions. Returning values of the last ones works
     *      because the last emitted DefiBridgeProcessed event corresponds to the `convert(...)` call.
     * @return outputValueA the amount of outputAssetA returned from the DeFi bridge interaction in this rollup
     * @return outputValueB the amount of outputAssetB returned from the DeFi bridge interaction in this rollup
     * @return isAsync a flag indicating whether the DeFi bridge interaction in this rollup was async
     */
    function _getDefiBridgeProcessedData()
        internal
        returns (uint256 outputValueA, uint256 outputValueB, bool isAsync)
    {
        Vm.Log[] memory logs = vm.getRecordedLogs();

        for (uint256 i; i < logs.length; ++i) {
            if (logs[i].topics[0] == BRIDGE_PROCESSED_EVENT_SIG) {
                (, outputValueA, outputValueB) = abi.decode(logs[i].data, (uint256, uint256, uint256));
            } else if (logs[i].topics[0] == ASYNC_BRIDGE_PROCESSED_EVENT_SIG) {
                // We don't return totalInputValue so there is no need to decode the event's data
                return (0, 0, true);
            }
        }
    }

    function _prepRollup() private {
        // Overwrite the rollup state hash
        {
            bytes32 rollupStateHash = keccak256(
                abi.encode(
                    uint256(nextRollupId),
                    0x18ceb5cd201e1cee669a5c3ad96d3c4e933a365b37046fc3178264bede32c68d,
                    0x298329c7d0936453f354e4a5eef4897296cc0bf5a66f2a528318508d2088dafa,
                    0x2fd2364bfe47ccb410eba3a958be9f39a8c6aca07db1abd15f5a211f51505071,
                    0x2e4ab7889ab3139204945f9e722c7a8fdb84e66439d787bd066c3d896dba04ea
                )
            );
            vm.store(address(rollupProcessor), bytes32(uint256(9)), rollupStateHash);
        }

        if (nextRollupId == 0) {
            // Overwrite the rollup state to zero (only verifier address)
            vm.store(
                address(rollupProcessor), bytes32(uint256(2)), bytes32(uint256(uint160(rollupProcessor.verifier())))
            );
        }
        if (mockVerifierCall) {
            vm.mockCall(rollupProcessor.verifier(), "", abi.encode(true));
        }
    }

    function _addDepositTx(
        bytes memory _encodedProofData,
        uint256 _encodedProofLocation,
        bytes memory _signatures,
        uint256 _sigIndex,
        uint256 id
    ) private returns (uint256, uint256) {
        DepositStruct memory deposit_ = depositsL2[id];

        address publicOwner = vm.addr(deposit_.privKey);

        bytes memory encoded = abi.encodePacked(
            uint8(ProofId.DEPOSIT), // 1
            bytes32("leaf1"), // 32 (33)
            bytes32("leaf2"), // 32 (65)
            bytes32("null1"), // 32 (97)
            bytes32("null2"), // 32 (129)
            bytes32(deposit_.amount + deposit_.fee), // 32 (161)
            publicOwner, // 20 (181)
            uint32(deposit_.assetId) // 4  (185)
        );

        assembly {
            mstore(add(_encodedProofData, _encodedProofLocation), mload(add(encoded, 0x20)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x20)), mload(add(encoded, 0x40)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x40)), mload(add(encoded, 0x60)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x60)), mload(add(encoded, 0x80)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x80)), mload(add(encoded, 0xa0)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0xa0)), mload(add(encoded, 0xc0)))
        }

        if (deposit_.digest != bytes32("")) {
            delete depositsL2[id];
            return (_encodedProofLocation + 0xb9, _sigIndex);
        }

        bytes memory full = abi.encodePacked(
            bytes32(uint256(ProofId.DEPOSIT)),
            bytes32("leaf1"),
            bytes32("leaf2"),
            bytes32("null1"),
            bytes32("null2"),
            bytes32(deposit_.amount + deposit_.fee),
            bytes32(uint256(uint160(publicOwner))),
            bytes32(deposit_.assetId)
        );

        bytes32 digest = keccak256(full);
        bytes32 hashedMessage = RollupProcessorLibrary.getSignedMessageForTxId(digest);
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(deposit_.privKey, hashedMessage);

        assembly {
            mstore(add(_signatures, _sigIndex), r)
            mstore(add(_signatures, add(_sigIndex, 0x20)), s)
            mstore(add(_signatures, add(_sigIndex, 0x40)), v)
        }
        delete depositsL2[id];
        return (_encodedProofLocation + 0xb9, _sigIndex + 0x60);
    }

    function _addWithdrawTx(bytes memory _encodedProofData, uint256 _encodedProofLocation, uint256 id)
        private
        returns (uint256)
    {
        WithdrawStruct memory withdraw_ = withdrawalsL2[id];

        bytes memory encoded = abi.encodePacked(
            uint8(ProofId.WITHDRAW), // 1
            bytes32("leaf1"), // 32 (33)
            bytes32("leaf2"), // 32 (65)
            bytes32("null1"), // 32 (97)
            bytes32("null2"), // 32 (129)
            bytes32(withdraw_.amount), // 32 (161)
            withdraw_.publicOwner, // 20 (181)
            uint32(withdraw_.assetId) // 4  (185)
        );

        assembly {
            mstore(add(_encodedProofData, _encodedProofLocation), mload(add(encoded, 0x20)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x20)), mload(add(encoded, 0x40)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x40)), mload(add(encoded, 0x60)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x60)), mload(add(encoded, 0x80)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x80)), mload(add(encoded, 0xa0)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0xa0)), mload(add(encoded, 0xc0)))
        }

        delete withdrawalsL2[id];

        return _encodedProofLocation + 0xb9;
    }

    function _addDefiTx(bytes memory _encodedProofData, uint256 _encodedProofLocation, uint256 id)
        private
        returns (uint256)
    {
        bytes memory encoded = abi.encodePacked(
            uint8(ProofId.DEFI_DEPOSIT), // 1
            bytes32("leaf1"), // 32 (33)
            bytes32("leaf2"), // 32 (65)
            bytes32("null1"), // 32 (97)
            bytes32("null2") // 32 (129)
        );

        assembly {
            mstore(add(_encodedProofData, _encodedProofLocation), mload(add(encoded, 0x20)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x20)), mload(add(encoded, 0x40)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x40)), mload(add(encoded, 0x60)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x60)), mload(add(encoded, 0x80)))
            mstore(add(_encodedProofData, add(_encodedProofLocation, 0x80)), mload(add(encoded, 0xa0)))
        }

        delete defiInteractionsL2[id];

        return _encodedProofLocation + 0x81;
    }

    function _encodeAsset(AztecTypes.AztecAsset memory _asset) private pure returns (uint256) {
        if (_asset.assetType == AztecTypes.AztecAssetType.VIRTUAL) {
            return (_asset.id & MASK_THIRTY_BITS) | VIRTUAL_ASSET_ID_FLAG;
        }
        return _asset.id & MASK_THIRTY_BITS;
    }
}
