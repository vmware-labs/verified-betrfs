abstract module TeamIfc {
    type TeamMember(==)
    type TeeShirtColor(==)
}

module TrainTeam refines TeamIfc {
    datatype TeamMember = Engineer | Conductor | Brakeperson
    function GetLeader() : TeamMember { Conductor }
}

abstract module UnionIfc refines TeamIfc {
    function GetRepresentative(member: TeamMember) : TeamMember
    {
        var rep:TeamMember :| true; rep
    }
}

module UnionizedTrain refines UnionIfc {
    // This tells us what sauce satisfies SandwichIfc.TeamIfc.Sauce,
    // which is why we can call TeamIfc.Pour.
    // But SandwichIfc.Spread now expects CubanSauce, but
    // TeamIfc.Pour is somehow a different type.
    import TeamIfc = TrainTeam
    // type TeamMember = TeamIfc.TeamMember // disallowed by Jon

    function GetRepForLeader() : TeamMember {
        GetRepresentative(TeamIfc.GetLeader())
    }
}
