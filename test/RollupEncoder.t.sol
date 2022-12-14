// SPDX-License-Identifier: Apache-2.0
// Copyright 2022 Aztec.
pragma solidity >=0.8.4;

import {Test} from "forge-std/Test.sol";

import {AztecTypes} from "../src/libraries/AztecTypes.sol";
import {RollupEncoder} from "../src/RollupEncoder.sol";

contract RollupEncoderTest is RollupEncoder, Test {
    uint256 internal constant ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;
    uint256 internal constant ROLLUP_BENEFICIARY_OFFSET = 4512; // ROLLUP_HEADER_LENGTH - 0x20

    AztecTypes.AztecAsset internal emptyAsset;

    constructor() RollupEncoder(0xFF1F2B4ADb9dF6FC8eAFecDcbF96A2B351680455) {}

    function testVirtualAssetFlagApplied(uint32 _assetId) public {
        uint256 assetId = bound(_assetId, 0, VIRTUAL_ASSET_ID_FLAG - 1);
        uint256 virtualAsset = assetId + VIRTUAL_ASSET_ID_FLAG;

        AztecTypes.AztecAsset memory decoded = _decodeAsset(virtualAsset);
        assertEq(decoded.erc20Address, address(0), "Virtual asset has erc20 address");
        assertEq(decoded.id, assetId, "Asset Id not matching");
        assertTrue(decoded.assetType == AztecTypes.AztecAssetType.VIRTUAL, "Not virtual");
    }

    function testNonVirtual(uint32 _assetId) public {
        uint256 assetId = bound(_assetId, 0, ROLLUP_PROCESSOR.getSupportedAssetsLength());

        address assetAddress = ROLLUP_PROCESSOR.getSupportedAsset(assetId);

        AztecTypes.AztecAsset memory decoded = _decodeAsset(assetId);

        assertEq(decoded.erc20Address, assetAddress, "asset address not matching");
        assertEq(decoded.id, assetId, "Asset Id not matching");
        if (assetAddress == address(0)) {
            assertTrue(decoded.assetType == AztecTypes.AztecAssetType.ETH, "Not eth");
        } else {
            assertTrue(decoded.assetType == AztecTypes.AztecAssetType.ERC20, "Not erc20");
        }
    }

    function testGetDefiBridgeProcessedData() public {
        uint256 outputValueAReference = 896;
        uint256 outputValueBReference = 351;

        vm.recordLogs();
        emit DefiBridgeProcessed(126, 12, 41, outputValueAReference, outputValueBReference, true, "");
        (uint256 outputValueA, uint256 outputValueB, bool isAsync) = _getDefiBridgeProcessedData();

        assertEq(outputValueA, outputValueAReference, "Incorrect outputValueA");
        assertEq(outputValueB, outputValueBReference, "Incorrect outputValueB");
        assertFalse(isAsync, "Interaction unexpectedly async");
    }

    function testGetDefiBridgeProcessedDataAsync() public {
        vm.recordLogs();
        emit AsyncDefiBridgeProcessed(126, 12, 1e18);
        (uint256 outputValueA, uint256 outputValueB, bool isAsync) = _getDefiBridgeProcessedData();

        assertEq(outputValueA, 0, "Incorrect outputValueA");
        assertEq(outputValueB, 0, "Incorrect outputValueB");
        assertTrue(isAsync, "Interaction unexpectedly async");
    }

    function testRollupBeneficiaryEncoding() public {
        address beneficiary = 0x508383c4cbD351dC2d4F632C65Ee9d2BC79612EC;
        this.setRollupBeneficiary(beneficiary);
        this.defiInteractionL2(5, emptyAsset, emptyAsset, emptyAsset, emptyAsset, 0, 0);
        (bytes memory encodedProofData,) = prepProcessorAndGetRollupBlock();
        address decodedBeneficiary = _extractRollupBeneficiary(encodedProofData);
        assertEq(decodedBeneficiary, beneficiary, "Decoded address does not match");
    }

    function testMiniDeposit() public {
        uint256 user1Priv = 123123123;
        address user1 = vm.addr(user1Priv);
        address user2 = address(0xdead);
        emit log_named_address("user ", user1);
        vm.deal(user1, 2 ether);
        vm.deal(user2, 0);

        emit log_named_decimal_uint("Balance R", address(ROLLUP_PROCESSOR).balance, 18);
        emit log_named_decimal_uint("Balance U", user2.balance, 18);

        vm.prank(user1);
        ROLLUP_PROCESSOR.depositPendingFunds{value: 2 ether}(0, 2 ether, user1, bytes32(""));

        emit log_named_uint("pending", ROLLUP_PROCESSOR.userPendingDeposits(0, user1));
        this.depositL2(0, 1 ether, 0, user1Priv);

        this.withdrawL2(0, 5 ether, user2);

        this.processRollup();

        emit log_named_uint("pending", ROLLUP_PROCESSOR.userPendingDeposits(0, user1));
        emit log_named_decimal_uint("Balance R", address(ROLLUP_PROCESSOR).balance, 18);
        emit log_named_decimal_uint("Balance U", user2.balance, 18);

        this.withdrawL2(0, 5 ether, user2);
        this.processRollup();

        emit log_named_uint("pending", ROLLUP_PROCESSOR.userPendingDeposits(0, user1));
        emit log_named_decimal_uint("Balance R", address(ROLLUP_PROCESSOR).balance, 18);
        emit log_named_decimal_uint("Balance U", user2.balance, 18);
    }

    function _decodeAsset(uint256 _assetId) internal view returns (AztecTypes.AztecAsset memory) {
        if (_assetId >> VIRTUAL_ASSET_ID_FLAG_SHIFT == 1) {
            return AztecTypes.AztecAsset({
                id: _assetId - VIRTUAL_ASSET_ID_FLAG,
                erc20Address: address(0),
                assetType: AztecTypes.AztecAssetType.VIRTUAL
            });
        } else {
            address erc20Address = ROLLUP_PROCESSOR.getSupportedAsset(_assetId);
            return AztecTypes.AztecAsset({
                id: _assetId,
                erc20Address: erc20Address,
                assetType: erc20Address == address(0) ? AztecTypes.AztecAssetType.ETH : AztecTypes.AztecAssetType.ERC20
            });
        }
    }

    // copied from Decoder.sol
    function _extractRollupBeneficiary(bytes memory _proofData) internal pure returns (address rollupBeneficiary) {
        /* solhint-disable no-inline-assembly */
        assembly {
            rollupBeneficiary := mload(add(_proofData, ROLLUP_BENEFICIARY_OFFSET))
            // Validate `rollupBeneficiary` is an address
            if gt(rollupBeneficiary, ADDRESS_MASK) { revert(0, 0) }
        }
        /* solhint-enable no-inline-assembly */
    }
}
