# Trusted concurrency framework

The .s files are arranged this way:

* VerificationObligations.s.dfy is the top-level theorem statement. The build
  system verifies that a Dafny module refines this module, and then blesses the
  corresponding executable.
