This directory is an experiment to confirm that we aren't over-counting module applications.
We were concerned because module application builds on the Dafny implementation's extreme
enthusiasm for cloning ASTs. We wanted to ensure that those cloned ASTs weren't leaking out
into the experiment.

To run the experiment:
make build/functor-application-linecount-test/system.i.lcreport
cat build/functor-application-linecount-test/system.i.lcreport

Successful (expected) result:
Observe that base.i.dfy has lots of lines of impl (I see 38), but the
application modules have much smaller numbers.

Negative (problematic) result:
If application modules have as many lines of impl as base, that suggests
they're incorporating copies of the base module in their output for
line-counting purposes.
