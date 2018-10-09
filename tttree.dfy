datatype Node =
	Leaf(value: int) |
	TwoNode(left: Node, pivot: int,
	        right: Node) |
	ThreeNode(left: Node, pivota: int,
	          middle: Node, pivotb: int,
						right: Node)

function SubtreeContents(tree: Node) : set<int>
{
	if tree.Leaf?
		then {tree.value}
	else if tree.TwoNode?
    then SubtreeContents(tree.left) + SubtreeContents(tree.right)
	else 
		SubtreeContents(tree.left) + SubtreeContents(tree.middle) + SubtreeContents(tree.right)
}

predicate ContentsAreLessThan(tree: Node, pivot: int) {
	forall lv :: lv in SubtreeContents(tree) ==> lv < pivot
}

predicate ContentsAreGreaterEqualThan(pivot: int, tree: Node) {
	forall lv :: lv in SubtreeContents(tree) ==> lv >= pivot
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
		else
			tree.pivota < tree.pivotb &&
			ContentsAreLessThan(tree.left, tree.pivota) &&
			ContentsAreGreaterEqualThan(tree.pivota, tree.middle) &&
			ContentsAreLessThan(tree.middle, tree.pivotb) &&
			ContentsAreGreaterEqualThan(tree.pivotb, tree.right) &&
			OrderedTree(tree.left) &&
			OrderedTree(tree.middle) &&
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
	else 
		1 + min(minHeight(tree.left), min(minHeight(tree.middle), minHeight(tree.right)))
}

function maxHeight(tree: Node) : int
{
	if tree.Leaf?
		then 0
	else if tree.TwoNode?
		then 1 + max(maxHeight(tree.left), maxHeight(tree.right))
	else
		1 + max(maxHeight(tree.left), max(maxHeight(tree.middle), maxHeight(tree.right)))
}

predicate balanced(tree: Node) {
	minHeight(tree) == maxHeight(tree)
}

predicate TTSubtree(tree: Node) {

	if tree.Leaf?
		then OrderedTree(tree) &&
		balanced(tree) &&
		SubtreeContents(tree) != {}
	else if tree.TwoNode?
		then OrderedTree(tree) &&
		balanced(tree) &&
		SubtreeContents(tree) != {} &&
		TTSubtree(tree.left) &&
		TTSubtree(tree.right)
	else
		OrderedTree(tree) &&
		balanced(tree) &&
		SubtreeContents(tree) != {} &&
		TTSubtree(tree.left) &&
		TTSubtree(tree.middle) &&
		TTSubtree(tree.right)
}

function Height(tree: Node) : int
	requires(balanced(tree));
{
	minHeight(tree)
}

method NodeContains(tree: Node, value: int) returns (present: bool)
    requires OrderedTree(tree);
    ensures present == (value in SubtreeContents(tree));
{
	if tree.Leaf? {
		present := value == tree.value;
	} else if tree.TwoNode? {
		if value < tree.pivot {
			present := NodeContains(tree.left, value);
		} else {
			present := NodeContains(tree.right, value);
		}
	} else {
		if value < tree.pivota {
			present := NodeContains(tree.left, value);
		} else if value < tree.pivotb {
			present := NodeContains(tree.middle, value);
		} else {
			present := NodeContains(tree.right, value);
		}
	}
}

datatype InsertionResult = InsertionResult(tree: Node, split: bool)
	
method InternalInsert(tree: Node, value: int) returns (result: InsertionResult)
	requires TTSubtree(tree);
	ensures TTSubtree(result.tree);
	ensures SubtreeContents(result.tree) == SubtreeContents(tree) + {value};
	ensures result.split ==> Height(result.tree) == Height(tree) + 1;
	ensures result.split ==> result.tree.TwoNode?;
	ensures !result.split ==> Height(result.tree) == Height(tree);
{
	if tree.Leaf? {
		if tree.value == value {
			result := InsertionResult(tree, false);
		} else if tree.value < value {
			var newright := Leaf(value);
			var newtree := TwoNode(tree, value, newright);
			assert(Height(newright) == Height(tree));
			assert(Height(newtree) == Height(tree) + 1);
			result := InsertionResult(newtree, true);
		} else {
			var newleft := Leaf(value);
			var newtree := TwoNode(newleft, tree.value, tree);
			assert(Height(newleft) == Height(tree));
			assert(Height(newtree) == Height(tree) + 1);
			result := InsertionResult(newtree, true);
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
				var newright := TwoNode(tree.middle, tree.pivotb, tree.right);
				assert(Height(newright) == Height(tree));
				var newtree := TwoNode(subresult.tree, tree.pivota, newright);
				assert(Height(newtree) == Height(tree) + 1);
				result := InsertionResult(newtree, true);
			}
		} else if value < tree.pivotb {
			var subresult := InternalInsert(tree.middle, value);
			if !subresult.split {
				result := InsertionResult(ThreeNode(tree.left, tree.pivota,
					                                  subresult.tree, tree.pivotb,
																						tree.right), false);
			} else {
				var newleft := TwoNode(tree.left, tree.pivota, subresult.tree.left);
				var newright := TwoNode(subresult.tree.right, tree.pivotb, tree.right);
				var newtree := TwoNode(newleft, subresult.tree.pivot, newright);
				assert(Height(newleft) == Height(tree));
				assert(Height(newright) == Height(tree));
				assert(Height(newtree) == Height(tree) + 1);
				result := InsertionResult(newtree, true);
				}
		} else {
			var subresult := InternalInsert(tree.right, value);
			if !subresult.split {
				result := InsertionResult(ThreeNode(tree.left, tree.pivota,
					                                  tree.middle, tree.pivotb,
																						subresult.tree), false);
			} else {
				var newleft := TwoNode(tree.left, tree.pivota, tree.middle);
				var newtree := TwoNode(newleft, tree.pivotb, subresult.tree);
				assert(Height(newleft) == Height(tree));
				assert(Height(newtree) == Height(tree) + 1);
				result := InsertionResult(newtree, true);
			}
		}
	} 
}

datatype Tree = EmptyTree | NonEmptyTree(root: Node)

predicate TTTree(tree: Tree) {
	tree.EmptyTree? || TTSubtree(tree.root)
}

function Contents(tree: Tree) : set<int>
{
	if tree.EmptyTree?
		then {}
	else
		SubtreeContents(tree.root)
}

method Contains(tree: Tree, value: int) returns (present: bool)
	requires(TTTree(tree));
	ensures(present == (value in Contents(tree)));
{
	if tree.EmptyTree? {
		present := false;
	} else { 
		present := NodeContains(tree.root, value);
	}
}

method Insert(tree: Tree, value: int) returns (newtree: Tree)
	requires(TTTree(tree));
	ensures(Contents(newtree) == Contents(tree) + {value});
	ensures(newtree.NonEmptyTree?);
{
	if tree.EmptyTree? {
		newtree := NonEmptyTree(Leaf(value));
	} else {
		var result := InternalInsert(tree.root, value);
		newtree := NonEmptyTree(result.tree);
	}
}
