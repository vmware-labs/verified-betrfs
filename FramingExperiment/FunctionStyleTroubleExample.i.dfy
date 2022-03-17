// Copyright 2018-2021 VMware, Inc., Microsoft Inc., Carnegie Mellon University, ETH Zurich, and University of Washington
// SPDX-License-Identifier: BSD-2-Clause

include "../lib/Base/Option.s.dfy"
include "HilbertChoose.i.dfy"

module FunctionStyleTroubleExample {
  import opened Options
  import opened HilbertChoose

  datatype TransitionLabel = LabelA | LabelB
  datatype Step = StepA(choice: nat) | StepB

  datatype Variables = Variables(a: nat, b: nat) {
    function DoA(lbl: TransitionLabel, choice: nat) : Option<Variables> {
      Some(this.(a := choice))
    }

    function DoB(lbl: TransitionLabel) : Option<Variables> {
      Some(this.(b := 2))
    }

    function NextStep(lbl: TransitionLabel, step: Step) : Option<Variables> {
      match step
        case StepA(choice) => DoA(lbl, choice)
        case StepB() => DoB(lbl)
    }

    function Next(lbl: TransitionLabel) : Option<Variables> {
      var step := ChooseIf(step => NextStep(lbl, step).Some?);
      if step.Some? then NextStep(lbl, step.value) else None
    }
  }

  lemma WhichNext(v: Variables, v': Variables, lbl: TransitionLabel, choice: nat)
    requires Some(v') == v.Next(lbl)
    requires Some(v') == v.DoA(lbl, choice)
  {
//    var p := step => v.NextStep(lbl, step).Some?;
//    var step1 := ChooseIf(p);
    var step := ChooseIf(step => v.NextStep(lbl, step).Some?);
    assert step.Some?;
    // What if v==(1,2) and step==StepB() or step==StepA(1)?
    assert step.value.StepA?;
    assert step == Some(StepA(choice));
//    assert step1 == step;
//    if step.None? {
//      assert p.requires(StepB) && p(StepB);
//      assert false;
//      assert step == Some(StepA);
//    }
//    if step.Some? && step.value.StepB? {
//      assert p.requires(StepB) && p(StepB);
////      assert Some(v') == v.DoB(lbl);
//      assert step == Some(StepA);
//    }
  }
}

