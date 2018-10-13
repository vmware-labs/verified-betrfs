function method min(a: int, b: int) : int
{
	if a < b
		then a
	else
		b
}

function method max(a: int, b: int) : int
{
	if a < b
		then b
	else
		a
}

datatype Endpoint = Open(point: int) | Closed(point: int)

datatype Interval = Interval(low: Endpoint, high: Endpoint)
	
predicate method IntervalIsEmpty(ival: Interval) {
	ival.low.point > ival.high.point ||
		(ival.low.point == ival.high.point && (ival.low.Open? || ival.high.Open?))
}

predicate method IntervalContains(ival: Interval, value: int)
{
	(if ival.low.Closed? then ival.low.point <= value else ival.low.point < value)	&&
		(if ival.high.Closed? then value <= ival.high.point else value < ival.high.point)
}

predicate method IsSubInterval(ival1: Interval, ival2: Interval)
	ensures IsSubInterval(ival1, ival2) ==> forall x: int :: IntervalContains(ival1, x) ==> IntervalContains(ival2, x);
{
	IntervalIsEmpty(ival1) ||
		((ival2.low.point <= ival1.low.point) &&
		(ival2.low.point == ival1.low.point ==> ival2.low.Closed? || ival1.low.Open?) &&
		(ival2.high.point >= ival1.high.point) &&
		(ival2.high.point == ival1.high.point ==> ival2.high.Closed? || ival1.high.Open?))
}

function method IntervalUnion(a: Interval, b: Interval) : Interval
	ensures IsSubInterval(a, IntervalUnion(a, b));
	ensures IsSubInterval(b, IntervalUnion(a, b));
{
	if IntervalIsEmpty(a) && IntervalIsEmpty(b) then
		Interval(Open(0), Open(0))
	else if IntervalIsEmpty(a) then
		b
	else if IntervalIsEmpty(b) then
		a
	else
		var low := min(a.low.point, b.low.point);
		var lowep := if a.low.Closed? || b.low.Closed? then Closed(low) else Open(low);
		var high := max(a.high.point, b.high.point);
		var highep := if a.high.Closed? || b.high.Closed? then Closed(high) else Open(high);
		Interval(lowep, highep)
}

function method IntervalUnion3(a: Interval, b: Interval, c: Interval) : Interval
	ensures IsSubInterval(a, IntervalUnion3(a, b, c));
	ensures IsSubInterval(b, IntervalUnion3(a, b,c ));
	ensures IsSubInterval(c, IntervalUnion3(a, b,c ));
{
	IntervalUnion(a, IntervalUnion(b, c))
}

datatype Node =
	Leaf(value: Interval) |
	TwoNode(left: Node, pivot: int, right: Node, interval: Interval) |
	ThreeNode(left: Node, pivota: int, middle: Node, pivotb: int, right: Node, interval: Interval)

function method SummaryInterval(tree: Node) : Interval {
	if tree.Leaf? then tree.value else tree.interval
}
	
function method mkTwoNode(left: Node, pivot: int, right: Node) : Node {
	TwoNode(left, pivot, right, IntervalUnion(SummaryInterval(left), SummaryInterval(right)))
}
						
function method mkThreeNode(left: Node, pivota: int, middle: Node, pivotb: int, right: Node) : Node {
	ThreeNode(left, pivota, middle, pivotb, right,
		IntervalUnion3(SummaryInterval(left), SummaryInterval(middle), SummaryInterval(right)))
}

function SubtreeContents(tree: Node) : set<Interval>
	ensures SubtreeContents(tree) != {};
{
	if tree.Leaf?
		then {tree.value}
	else if tree.TwoNode?
    then SubtreeContents(tree.left) + SubtreeContents(tree.right)
	else 
		SubtreeContents(tree.left) + SubtreeContents(tree.middle) + SubtreeContents(tree.right)
}

predicate OrderedTree(tree: Node)
{
    if tree.Leaf?
			then true
		else if tree.TwoNode?
      then
			(forall intrvl: Interval :: intrvl in SubtreeContents(tree) ==> IsSubInterval(intrvl, tree.interval)) &&
			(forall intrvl: Interval :: intrvl in SubtreeContents(tree.left) ==> intrvl.low.point <= tree.pivot) &&
			(forall intrvl: Interval :: intrvl in SubtreeContents(tree.right) ==> tree.pivot <= intrvl.low.point) &&
			OrderedTree(tree.left) &&
			OrderedTree(tree.right)
		else
			tree.pivota <= tree.pivotb &&
			(forall intrvl: Interval :: intrvl in SubtreeContents(tree) ==> IsSubInterval(intrvl, tree.interval)) &&
			(forall intrvl: Interval :: intrvl in SubtreeContents(tree.left) ==> intrvl.low.point <= tree.pivota) &&
			(forall intrvl: Interval :: intrvl in SubtreeContents(tree.middle) ==> tree.pivota <= intrvl.low.point &&
			                                                               intrvl.low.point <= tree.pivotb) &&
			(forall intrvl: Interval :: intrvl in SubtreeContents(tree.right) ==> tree.pivotb <= intrvl.low.point) &&
			OrderedTree(tree.left) &&
			OrderedTree(tree.middle) &&
			OrderedTree(tree.right)
}

function method StabbingQuery(tree: Node, value: int) : set<Interval>
  requires OrderedTree(tree);
	ensures StabbingQuery(tree, value) ==
	 	set ival : Interval | ival in SubtreeContents(tree) && IntervalContains(ival, value)
{
	match tree {
		case Leaf(ival) =>
			if IntervalContains(ival, value) then {ival} else {}
		case TwoNode(left, pivot, right, sumintrvl) =>
			if !IntervalContains(sumintrvl, value) then
			{}
			else
				StabbingQuery(left, value) + StabbingQuery(right, value)
		case ThreeNode(left, pivota, middle, pivotb, right, sumintrvl) =>
			if !IntervalContains(sumintrvl, value) then
			{}
			else
				StabbingQuery(left, value) + StabbingQuery(middle, value) + StabbingQuery(right, value)
	}
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

predicate Balanced(tree: Node)
{
	minHeight(tree) == maxHeight(tree) &&
		(tree.TwoNode? ==> Balanced(tree.left) && Balanced(tree.right)) &&
		(tree.ThreeNode? ==> Balanced(tree.left) && Balanced(tree.middle) && Balanced(tree.right))
}

predicate ITTSubtree(tree: Node) {

	if tree.Leaf? then
		OrderedTree(tree) &&
		Balanced(tree) &&
		SubtreeContents(tree) != {}
	else if tree.TwoNode? then
		OrderedTree(tree) &&
		Balanced(tree) &&
		SubtreeContents(tree) != {} &&
		ITTSubtree(tree.left) &&
		ITTSubtree(tree.right)
	else
		OrderedTree(tree) &&
		Balanced(tree) &&
		SubtreeContents(tree) != {} &&
		ITTSubtree(tree.left) &&
		ITTSubtree(tree.middle) &&
		ITTSubtree(tree.right)
}

function method Height(tree: Node) : int
	requires Balanced(tree);
	ensures Height(tree) == minHeight(tree);
	ensures Height(tree) == maxHeight(tree);
{
	if tree.Leaf? then 0 else 1 + Height(tree.left)
}

datatype InsertionResult = InsertionResult(tree: Node, split: bool)
	
method InternalInsert(tree: Node, intrvl: Interval) returns (result: InsertionResult)
	requires ITTSubtree(tree);
	ensures ITTSubtree(result.tree);
	ensures SubtreeContents(result.tree) == SubtreeContents(tree) + {intrvl};
	ensures result.split ==> Height(result.tree) == Height(tree) + 1;
	ensures result.split ==> result.tree.TwoNode?;
	ensures !result.split ==> Height(result.tree) == Height(tree);
{
	if tree.Leaf? {
		if tree.value == intrvl {
			result := InsertionResult(tree, false);
		} else if tree.value.low.point < intrvl.low.point {
			var newright := Leaf(intrvl);
			var newtree := mkTwoNode(tree, intrvl.low.point, newright);
			assert(Height(newright) == Height(tree));
			assert(Height(newtree) == Height(tree) + 1);
			result := InsertionResult(newtree, true);
		} else {
			var newleft := Leaf(intrvl);
			var newtree := mkTwoNode(newleft, tree.value.low.point, tree);
			assert(Height(newleft) == Height(tree));
			assert(Height(newtree) == Height(tree) + 1);
			result := InsertionResult(newtree, true);
		}
	} else if tree.TwoNode? {
		if intrvl.low.point < tree.pivot {
			var subresult := InternalInsert(tree.left, intrvl);
			if !subresult.split {
				result := InsertionResult(mkTwoNode(subresult.tree, tree.pivot, tree.right), false);
			} else {
				result := InsertionResult(mkThreeNode(subresult.tree.left, subresult.tree.pivot,
					                                   subresult.tree.right, tree.pivot,
																					   tree.right),
																 false);
			}
		} else {
			var subresult := InternalInsert(tree.right, intrvl);
			if !subresult.split {
				result := InsertionResult(mkTwoNode(tree.left, tree.pivot, subresult.tree), false);
			} else {
				result := InsertionResult(mkThreeNode(tree.left, tree.pivot,
			                		                   subresult.tree.left, subresult.tree.pivot,
																		 				 subresult.tree.right), false);
			}
		}
	} else if tree.ThreeNode? {
		if intrvl.low.point < tree.pivota {
			var subresult := InternalInsert(tree.left, intrvl);
			if !subresult.split {
				result := InsertionResult(mkThreeNode(subresult.tree, tree.pivota,
					                                   tree.middle, tree.pivotb,
																						 tree.right), false);
			} else {
				var newright := mkTwoNode(tree.middle, tree.pivotb, tree.right);
				assert(Height(newright) == Height(tree));
				var newtree := mkTwoNode(subresult.tree, tree.pivota, newright);
				assert(Height(newtree) == Height(tree) + 1);
				result := InsertionResult(newtree, true);
			}
		} else if intrvl.low.point < tree.pivotb {
			var subresult := InternalInsert(tree.middle, intrvl);
			if !subresult.split {
				result := InsertionResult(mkThreeNode(tree.left, tree.pivota,
					                                   subresult.tree, tree.pivotb,
																						 tree.right), false);
			} else {
				var newleft := mkTwoNode(tree.left, tree.pivota, subresult.tree.left);
				var newright := mkTwoNode(subresult.tree.right, tree.pivotb, tree.right);
				var newtree := mkTwoNode(newleft, subresult.tree.pivot, newright);
				assert(Height(newleft) == Height(tree));
				assert(Height(newright) == Height(tree));
				assert(Height(newtree) == Height(tree) + 1);
				result := InsertionResult(newtree, true);
				}
		} else {
			var subresult := InternalInsert(tree.right, intrvl);
			if !subresult.split {
				result := InsertionResult(mkThreeNode(tree.left, tree.pivota,
					                                   tree.middle, tree.pivotb,
																						 subresult.tree), false);
			} else {
				var newleft := mkTwoNode(tree.left, tree.pivota, tree.middle);
				var newtree := mkTwoNode(newleft, tree.pivotb, subresult.tree);
				assert(Height(newleft) == Height(tree));
				assert(Height(newtree) == Height(tree) + 1);
				result := InsertionResult(newtree, true);
			}
		}
	} 
}

// datatype Tree = EmptyTree | NonEmptyTree(root: Node)

// predicate TTTree(tree: Tree) {
// 	tree.EmptyTree? || TTSubtree(tree.root)
// }

// function Contents(tree: Tree) : set<int>
// {
// 	if tree.EmptyTree?
// 		then {}
// 	else
// 		SubtreeContents(tree.root)
// }

// method Contains(tree: Tree, value: int) returns (present: bool)
// 	requires(TTTree(tree));
// 	ensures(present == (value in Contents(tree)));
// {
// 	if tree.EmptyTree? {
// 		present := false;
// 	} else { 
// 		present := NodeContains(tree.root, value);
// 	}
// }

// method Insert(tree: Tree, value: int) returns (newtree: Tree)
// 	requires(TTTree(tree));
// 	ensures(TTTree(newtree));
// 	ensures(Contents(newtree) == Contents(tree) + {value});
// 	ensures(newtree.NonEmptyTree?);
// {
// 	if tree.EmptyTree? {
// 		newtree := NonEmptyTree(Leaf(value));
// 	} else {
// 		var result := InternalInsert(tree.root, value);
// 		newtree := NonEmptyTree(result.tree);
// 	}
// }
