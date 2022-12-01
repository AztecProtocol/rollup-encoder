pragma solidity ^0.8.0;

/**
 * @notice Errors and events copied from RollupProcessorV2.
 * @dev This contract is extended by RollupEncoder in order for the errors to get properly resolved in Foundry tests.
 */
contract EventsErrorsV2 {
    /*----------------------------------------
    ERROR TAGS
    ----------------------------------------*/

    error PAUSED();
    error NOT_PAUSED();
    error LOCKED_NO_REENTER();
    error INVALID_PROVIDER();
    error THIRD_PARTY_CONTRACTS_FLAG_NOT_SET();
    error INSUFFICIENT_DEPOSIT();
    error INVALID_ADDRESS_NO_CODE();
    error INVALID_ASSET_GAS();
    error INVALID_ASSET_ID();
    error INVALID_ASSET_ADDRESS();
    error INVALID_BRIDGE_GAS();
    error INVALID_BRIDGE_CALL_DATA();
    error INVALID_BRIDGE_ADDRESS();
    error INVALID_ESCAPE_BOUNDS();
    error INCONSISTENT_BRIDGE_CALL_DATA();
    error BRIDGE_WITH_IDENTICAL_INPUT_ASSETS(uint256 inputAssetId);
    error BRIDGE_WITH_IDENTICAL_OUTPUT_ASSETS(uint256 outputAssetId);
    error ZERO_TOTAL_INPUT_VALUE();
    error ARRAY_OVERFLOW();
    error MSG_VALUE_WRONG_AMOUNT();
    error INSUFFICIENT_ETH_PAYMENT();
    error WITHDRAW_TO_ZERO_ADDRESS();
    error DEPOSIT_TOKENS_WRONG_PAYMENT_TYPE();
    error INSUFFICIENT_TOKEN_APPROVAL();
    error NONZERO_OUTPUT_VALUE_ON_NOT_USED_ASSET(uint256 outputValue);
    error INCORRECT_STATE_HASH(bytes32 oldStateHash, bytes32 newStateHash);
    error INCORRECT_DATA_START_INDEX(uint256 providedIndex, uint256 expectedIndex);
    error INCORRECT_PREVIOUS_DEFI_INTERACTION_HASH(
        bytes32 providedDefiInteractionHash, bytes32 expectedDefiInteractionHash
    );
    error PUBLIC_INPUTS_HASH_VERIFICATION_FAILED(uint256, uint256);
    error PROOF_VERIFICATION_FAILED();
    error PENDING_CAP_SURPASSED();
    error DAILY_CAP_SURPASSED();

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
    event AssetAdded(uint256 indexed assetId, address indexed assetAddress, uint256 assetGasLimit);
    event BridgeAdded(uint256 indexed bridgeAddressId, address indexed bridgeAddress, uint256 bridgeGasLimit);
    event RollupProviderUpdated(address indexed providerAddress, bool valid);
    event VerifierUpdated(address indexed verifierAddress);
    event AllowThirdPartyContractsUpdated(bool allowed);
    event DefiBridgeProxyUpdated(address defiBridgeProxy);
    event Paused(address account);
    event Unpaused(address account);
    event DelayBeforeEscapeHatchUpdated(uint32 delay);
    event AssetCapUpdated(uint256 assetId, uint256 pendingCap, uint256 dailyCap);
    event CappedUpdated(bool isCapped);
}
