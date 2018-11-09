datatype Node =
	Leaf(value: int) |
	TwoNode(left: Node, pivot: int,
	        right: Node) |
	ThreeNode(left: Node, pivota: int,
	          middle: Node, pivotb: int,
						right: Node) |
	FourNode(left: Node, pivot1: int,
	         middle1: Node, pivot2: int,
					 middle2: Node, pivot3: int,
					 right: Node)

datatype Tree = EmptyTree | NonEmptyTree(root: Node)
					 
function Contents(tree: Node) : set<int>
{
	if tree.Leaf?
		then {tree.value}
	else if tree.TwoNode?
    then Contents(tree.left) + Contents(tree.right)
	else if tree.ThreeNode?
		then Contents(tree.left) + Contents(tree.middle) + Contents(tree.right)
	else 
		Contents(tree.left) + Contents(tree.middle1) +
    Contents(tree.middle2) + Contents(tree.right)
}

predicate ContentsAreLessThan(tree: Node, pivot: int) {
	forall lv :: lv in Contents(tree) ==> lv < pivot
}

predicate ContentsAreGreaterEqualThan(pivot: int, tree: Node) {
	forall lv :: lv in Contents(tree) ==> lv >= pivot
}

predicate OrderedTree(tree: Node) {
    if tree.Leaf?
			then true
		else if tree.TwoNode?
      then
			ContentsAreLessThan(tree.left, tree.pivot) &&
			ContentsAreGreaterEqualThan(tree.pivot, tree.right) &&
			OrderedTree(tree.left) &&
			OrderedTree(tree.right)
		else if tree.ThreeNode?
			then
			tree.pivota < tree.pivotb &&
			ContentsAreLessThan(tree.left, tree.pivota) &&
			ContentsAreGreaterEqualThan(tree.pivota, tree.middle) &&
			ContentsAreLessThan(tree.middle, tree.pivotb) &&
			ContentsAreGreaterEqualThan(tree.pivotb, tree.right) &&
			OrderedTree(tree.left) &&
			OrderedTree(tree.middle) &&
			OrderedTree(tree.right)
		else
			tree.pivot1 < tree.pivot2 &&
			tree.pivot2 < tree.pivot3 &&
			ContentsAreLessThan(tree.left, tree.pivot1) &&
			ContentsAreGreaterEqualThan(tree.pivot1, tree.middle1) &&
			ContentsAreLessThan(tree.middle1, tree.pivot2) &&
			ContentsAreGreaterEqualThan(tree.pivot2, tree.middle2) &&
			ContentsAreLessThan(tree.middle2, tree.pivot3) &&
			ContentsAreGreaterEqualThan(tree.pivot3, tree.right) &&
			OrderedTree(tree.left) &&
			OrderedTree(tree.middle1) &&
			OrderedTree(tree.middle2) &&
			OrderedTree(tree.right)

}

function min(a: int, b: int) : int
{
	if a < b
		then a
	else
		b
}

function max(a: int, b: int) : int
{
	if a < b
		then b
	else
		a
}

function minHeight(tree: Node) : int
{
	if tree.Leaf?
		then 0
	else if tree.TwoNode?
		then 1 + min(minHeight(tree.left), minHeight(tree.right))
	else if tree.ThreeNode?
		then 1 + min(minHeight(tree.left), min(minHeight(tree.middle), minHeight(tree.right)))
	else
		1 + min(min(minHeight(tree.left), minHeight(tree.middle1)),
		        min(minHeight(tree.middle2), minHeight(tree.right)))
}

function maxHeight(tree: Node) : int
{
	if tree.Leaf?
		then 0
	else if tree.TwoNode?
		then 1 + max(maxHeight(tree.left), maxHeight(tree.right))
	else if tree.ThreeNode?
		then 1 + max(maxHeight(tree.left), max(maxHeight(tree.middle), maxHeight(tree.right)))
	else
		1 + max(max(maxHeight(tree.left), maxHeight(tree.middle1)),
		        max(maxHeight(tree.middle2), maxHeight(tree.right)))
}

predicate balanced(tree: Node) {
	minHeight(tree) == maxHeight(tree)
}

predicate TTFTree(tree: Node) {

	if tree.Leaf?
		then OrderedTree(tree) &&
		balanced(tree) &&
		Contents(tree) != {}
	else if tree.TwoNode?
		then OrderedTree(tree) &&
		balanced(tree) &&
		Contents(tree) != {} &&
		TTFTree(tree.left) &&
		TTFTree(tree.right)
	else if tree.ThreeNode?
		then OrderedTree(tree) &&
		balanced(tree) &&
		Contents(tree) != {} &&
		TTFTree(tree.left) &&
		TTFTree(tree.middle) &&
		TTFTree(tree.right)
	else
		OrderedTree(tree) &&
		balanced(tree) &&
		Contents(tree) != {} &&
		TTFTree(tree.left) &&
		TTFTree(tree.middle1) &&
		TTFTree(tree.middle2) &&
		TTFTree(tree.right)
}

function Height(tree: Node) : int
	requires(balanced(tree));
{
	minHeight(tree)
}

method Contains(tree: Node, value: int) returns (present: bool)
    requires OrderedTree(tree);
    ensures present == (value in Contents(tree));
{
	if tree.Leaf? {
		present := value == tree.value;
	} else if tree.TwoNode? {
		if value < tree.pivot {
			present := Contains(tree.left, value);
		} else {
			present := Contains(tree.right, value);
		}
	} else if tree.ThreeNode? {
		if value < tree.pivota {
			present := Contains(tree.left, value);
		} else if value < tree.pivotb {
			present := Contains(tree.middle, value);
		} else {
			present := Contains(tree.right, value);
		}
	} else if tree.FourNode? {
		if value < tree.pivot1 {
			present := Contains(tree.left, value);
		} else if value < tree.pivot2 {
			present := Contains(tree.middle1, value);
		} else if value < tree.pivot3 {
			present := Contains(tree.middle2, value);
		} else {
			present := Contains(tree.right, value);
		}
	}
}

datatype InsertionResult = InsertionResult(tree: Node, split: bool)

method InternalInsert(tree: Node, value: int) returns (result: InsertionResult)
	requires TTFTree(tree);
	ensures result.split ==> Height(result.tree) == Height(tree) + 1;
	ensures result.split ==> result.tree.TwoNode?;
	ensures !result.split ==> Height(result.tree) == Height(tree);
{
	if tree.Leaf? {
		if tree.value == value {
			result := InsertionResult(tree, false);
		} else if tree.value < value {
			result := InsertionResult(TwoNode(tree, value, Leaf(value)), true);
		} else {
			result := InsertionResult(TwoNode(Leaf(value), tree.value, tree), true);
		}
	} else if tree.TwoNode? {
		if value < tree.pivot {
			var subresult := InternalInsert(tree.left, value);
			if !subresult.split {
				result := InsertionResult(TwoNode(subresult.tree, tree.pivot, tree.right), false);
			} else {
				result := InsertionResult(ThreeNode(subresult.tree.left, subresult.tree.pivot,
					                                 subresult.tree.right, tree.pivot,
																					 tree.right), false);
			}
		} else {
			var subresult := InternalInsert(tree.right, value);
			if !subresult.split {
				result := InsertionResult(TwoNode(tree.left, tree.pivot, subresult.tree), false);
			} else {
				result := InsertionResult(ThreeNode(tree.left, tree.pivot,
			                		                  subresult.tree.left, subresult.tree.pivot,
																						subresult.tree.right), false);
			}
		}
	} else if tree.ThreeNode? {
		if value < tree.pivota {
			var subresult := InternalInsert(tree.left, value);
			if !subresult.split {
				result := InsertionResult(ThreeNode(subresult.tree, tree.pivota,
					                                  tree.middle, tree.pivotb,
																						tree.right), false);
			} else {
				result := InsertionResult(FourNode(subresult.tree.left, subresult.tree.pivot,
					                                 subresult.tree.right, tree.pivota,
																					 tree.middle, tree.pivotb,
																					 tree.right), false);
			}
		} else if value < tree.pivotb {
			var subresult := InternalInsert(tree.middle, value);
			if !subresult.split {
				result := InsertionResult(ThreeNode(tree.left, tree.pivota,
					                                  subresult.tree, tree.pivotb,
																						tree.right), false);
			} else {
				result := InsertionResult(FourNode(tree.left, tree.pivota,
			                                     subresult.tree.left, subresult.tree.pivot,
																					 subresult.tree.right, tree.pivotb,
																					 tree.right), false);
				}
		} else {
			var subresult := InternalInsert(tree.right, value);
			if !subresult.split {
				result := InsertionResult(ThreeNode(tree.left, tree.pivota,
					                                  tree.middle, tree.pivotb,
																						subresult.tree), false);
			} else {
				result := InsertionResult(FourNode(tree.left, tree.pivota,
			                                     tree.middle, tree.pivotb,
																					 subresult.tree.left, subresult.tree.pivot,
																					 subresult.tree.right), false);
			}
		}
	} else { /* tree.FourNode? */ 
	 	if value < tree.pivot1 {
			var subresult := InternalInsert(tree.left, value);
			if subresult.NoSplit? {
				result := NoSplit(FourNode(subresult.tree, tree.pivot1,
					                         tree.middle1, tree.pivot2,
					                         tree.middle2, tree.pivot3,
																	 tree.right));
	 		} else {
				result := Split(TwoNode(subresult.left, subresult.pivot, subresult.right),
					              tree.pivot1,
												ThreeNode(tree.middle1, tree.pivot2,
												          tree.middle2, tree.pivot3,
																	tree.right));
			}
		} else if value < tree.pivot2 {
			var subresult := InternalInsert(tree.middle1, value);
			if subresult.NoSplit? {
				result := NoSplit(FourNode(tree.left, tree.pivot1,
					                         subresult.tree, tree.pivot2,
																	 tree.middle2, tree.pivot3,
																	 tree.right));
			} else {
				result := Split(ThreeNode(tree.left, tree.pivot1,
					                        subresult.left, subresult.pivot, 
																	subresult.right),
												tree.pivot2,
												TwoNode(tree.middle2, tree.pivot3, tree.right));
			}
		} else if value < tree.pivot3 {
			var subresult := InternalInsert(tree.middle2, value);
			if subresult.NoSplit? {
				result := NoSplit(FourNode(tree.left, tree.pivot1,
					                         tree.middle1, tree.pivot2,
																	 subresult.tree, tree.pivot3,
																	 tree.right));
			} else {
				result := Split(TwoNode(tree.left, tree.pivot1, tree.middle1),
					              tree.pivot2, 
												ThreeNode(subresult.right, subresult.pivot,
												          subresult.left, tree.pivot3,
																	tree.right));
			}
		} else {
			var subresult := InternalInsert(tree.right, value);
			if subresult.NoSplit? {
				result := NoSplit(FourNode(tree.left, tree.pivot1,
					                         tree.middle1, tree.pivot2,
																	 tree.middle2, tree.pivot3,
																	 subresult.tree));
			} else {
				result := Split(ThreeNode(tree.left, tree.pivot1,
					                        tree.middle1, tree.pivot2,
																	tree.middle2),
												tree.pivot3,
												TwoNode(subresult.right, subresult.pivot, subresult.left));
			}
		}
 	}
}
