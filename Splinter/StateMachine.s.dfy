// TODO delete vestigial
abstract module StateMachine {
  type Variables(==,!new)

  predicate Init(v: Variables)

  predicate Next(v: Variables, v': Variables)
}
