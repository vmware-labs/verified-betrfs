In a verified system, it is important to understand both the guarantees being provided and the assumptions being made. Here, we document the guarantees and assumptions provided by VeriBetrFS.

VeriBetrFS currently provides a verified key-value store component.

### Guarantees

 * Key/value dictionary specification. State of the system is a map (key -> value).
 * Under normal operation, the result of a query will be the last value inserted for that key.
 * If a crash (e.g., system restart, power failure, etc.) occurs, the state of the system will revert to a consistent state no earlier that the last completed 	‘sync’ operation.
 * **Relevant files**
    * `MapSpec/MapSpec.s.dfy`
    * `MapSpec/ThreeStateVersioned.s.dfy`

### Assumptions

 * Our main system assumptions about the disk model.
   * We assume an asynchronous disk model, where reads and writes may be re-ordered.
   * We do not attempt to model overlapping reads and writes; we consider this ‘undefined behavior’.
   * The disk may randomly corrupt its data, but when it does so, it does not produce a checksum-valid block (using a [CRC32-C](https://en.wikipedia.org/wiki/Cyclic_redundancy_check) checksum).
     * VeriBetrFS is robust to disk corruption only in the sense that it will detect it and, as a result, fail to provide corrupted data to its client, but VeriBetrFS is not an error-correcting system, so it will not recover the true data.
 * **Relevant files**
    * `ByteBlockCacheSystem/AsyncDiskModel.s.dfy`

### Trusted Code

In order to document which files contain trusted assumptions, we use the file name extension. Files ending in `.s.dfy` compose all of our ‘trusted’ Dafny code. Files ending in `.i.dfy` compose our ‘untrusted’ Dafny code. The Dafny verifier checks that the implementation code and proof work in the `.i.dfy` files meets the obligations demanded by the `.s.dfy` files. These `.s.dfy` files document, _mathematically_, the guarantees and assumptions stated in English above.

Our entire Trusted Code Base (TCB) comprises:

 * All `.s` files in the repository.
 * The Dafny verifier, and its C++ code-generation.
 * The C++ compiler (currently clang).
 * The hardware, kernel, execution environment, etc.
 * Our [extensions to the Dafny language.](https://github.com/secure-foundations/dafny/tree/inout/Docs/Linear)
 * The `.cpp` files in `framework/` (especially `Framework.cpp`) which provide a layer between our Dafny-facing disk API and the operating system's aio API.
 * Extern functions that provide access to other useful system utilities (`lib/Lang/System/`).

Some of these items are in scope for VeriBetrFS, while others are not.

In particular, it's healthy for us to try to slim down on the files in `framework/` and `.s` files where possible.

### Other limitations

Our main limitation is that we don't prove liveness. Thus, while we do show that VeriBetrFS does not return incorrect answers, and while we show that we do not lose data (subject to no corruptions occurring), we do not actually ensure that any operation is guaranteed to complete.

However, we do note that IronFleet (an ‘intellectual predecessor’ to VeriBetrFS) has proved liveness. Proving liveness for VeriBetrFS would, however, be a significant undertaking (depending on assumptions and guarantees), and we currently consider it less valuable than its integrity guarantees.
