# Splinter Verification 

Work on verifying an implementation of the SplinterDB key-value store.

Initially this work was being done in Dafny. The Dafny proofs live in this folder (`verified-betrfs/Splinter/`).

We are now working on a Rust implementation (and corresponding proof of correctness) using `verus` which lives in
`verified-betrfs/Splinter/src/`.

## Proof Layout

For a diagram of the refinement proof structure we're building in the `verus` see [`splinter/docs/refinement-hierarchy.svg proof`](https://github.com/vmware-labs/verified-betrfs/blob/splinter/docs/refinement-hierarchy.svg).


## Commands

`$verus -Zunpretty=expanded bundle.rs` to get expanded macro representation of a verus file.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs`
To verify just a single module.

`$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs --triggers-silent --expand-errors --multiple-errors 1`

To disable "Recommends" checks (since `verus` will sometimes incorrectly warn about recommends clauses
not being satisfied when they are provably satisfied).
```
--no-auto-recommends-check
```

If you find yourself buried in error output, use this command to only get the top (and also get it in color):
```
$verus --verify-module coordination_layer::CoordinationSystemRefinement_v bundle.rs --triggers-silent --expand-errors --multiple-errors 2 --color=always 2>&1 | head -n 50
```

### Pushing `.record-history` History

If you're using the `record-history` feature of verus, here's instructions for how to push the history:
```
cd .record-history/git
RECORDED_ITEMS=`git log --all | grep 'record-history-ref-hash' | wc -l`
echo Recorded $RECORDED_ITEMS verus runs, pushing...
git push --all target
echo Pushed all branches.
```

## Verus

We use it. "Documentation" here: https://github.com/verus-lang/verus/tree/main/source/pervasive
