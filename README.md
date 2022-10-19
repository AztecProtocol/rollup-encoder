# Rollup Encoder

`RollupEncoder` is a contract which allows for creation of Aztec Connect rollup blocks without running the L2 infrastructure (sequencer, prover...).
The goal of this project is to give bridge developers an easy way to test their contracts (no typescript, just solidity + foundry).

An example of how to use this encoder can be found in our [aztec-connect-bridges](https://github.com/AztecProtocol/aztec-connect-bridges#aztec-connect-bridges). 