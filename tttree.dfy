datatype Node<Value> =
	Leaf(key: int, value: Value) |
	TwoNode(left: Node, pivot: int,
	        right: Node) |
	ThreeNode(left: Node, pivota: int,
	          middle: Node, pivotb: int,
						right: Node)

function merge_maps<U,T>(mapa: map<U,T>, mapb: map<U,T>) : map<U,T>
	ensures merge_maps(mapa, mapb).Keys == mapa.Keys + mapb.Keys;
	ensures forall k :: k in merge_maps(mapa, mapb).Keys && k !in mapb.Keys ==>
		merge_maps(mapa, mapb)[k] == mapa[k];
	ensures forall k :: k in merge_maps(mapa, mapb).Keys && k !in mapa.Keys ==>
		merge_maps(mapa, mapb)[k] == mapb[k];
	ensures forall k :: k in merge_maps(mapa, mapb).Keys && k in mapa.Keys * mapb.Keys ==>
		merge_maps(mapa, mapb)[k] == mapa[k] || merge_maps(mapa, mapb)[k] == mapb[k];
{
	map x : U | (x in mapa.Keys + mapb.Keys) :: if x in mapa then mapa[x] else mapb[x]
}

function SubtreeContents<Value>(tree: Node<Value>) : map<int, Value>
	ensures SubtreeContents(tree).Keys != {};
{
	if tree.Leaf? then
		var r := map[tree.key := tree.value];
		assert tree.key in r; // observe that r is not friggin empty
		r
	else if tree.TwoNode?
    then merge_maps(SubtreeContents(tree.left), SubtreeContents(tree.right))
	else 
		merge_maps(
		merge_maps(SubtreeContents(tree.left), SubtreeContents(tree.middle)),
		SubtreeContents(tree.right))
}

predicate ContentsAreLessThan(tree: Node, pivot: int) {
	forall lv :: lv in SubtreeContents(tree).Keys ==> lv < pivot
}

predicate ContentsAreGreaterEqualThan(pivot: int, tree: Node) {
	forall lv :: lv in SubtreeContents(tree).Keys ==> lv >= pivot
}

predicate OrderedTree(tree: Node) {
    if tree.Leaf?
			then SubtreeContents(tree).Keys != {}
		else if tree.TwoNode?
      then
			ContentsAreLessThan(tree.left, tree.pivot) &&
			ContentsAreGreaterEqualThan(tree.pivot, tree.right) &&
			SubtreeContents(tree).Keys != {} &&
			OrderedTree(tree.left) &&
			OrderedTree(tree.right)
		else
			tree.pivota < tree.pivotb &&
			ContentsAreLessThan(tree.left, tree.pivota) &&
			ContentsAreGreaterEqualThan(tree.pivota, tree.middle) &&
			ContentsAreLessThan(tree.middle, tree.pivotb) &&
			ContentsAreGreaterEqualThan(tree.pivotb, tree.right) &&
			SubtreeContents(tree).Keys != {} &&
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
		balanced(tree)
	else if tree.TwoNode?
		then OrderedTree(tree) &&
		balanced(tree) &&
		TTSubtree(tree.left) &&
		TTSubtree(tree.right)
	else
		OrderedTree(tree) &&
		balanced(tree) &&
		TTSubtree(tree.left) &&
		TTSubtree(tree.middle) &&
		TTSubtree(tree.right)
}

function Height(tree: Node) : int
	requires(balanced(tree));
{
	minHeight(tree)
}

datatype QueryResult<Value> = KeyDoesNotExist | ValueForKey(value: Value)

function method QuerySubtree<Value>(tree: Node<Value>, key: int) : QueryResult<Value>
    requires OrderedTree(tree);
    ensures QuerySubtree(tree, key) == KeyDoesNotExist <==>
			(key !in SubtreeContents(tree));
		ensures QuerySubtree(tree, key).ValueForKey? <==>
			(key in SubtreeContents(tree) && SubtreeContents(tree)[key] == QuerySubtree(tree, key).value);
{
	if tree.Leaf? && tree.key == key then
		ValueForKey(tree.value)
	else if tree.Leaf? && tree.key != key then
		KeyDoesNotExist
	else if tree.TwoNode? && key < tree.pivot then
		QuerySubtree(tree.left, key)
	else if tree.TwoNode? && key >= tree.pivot then
		QuerySubtree(tree.right, key)
	else if tree.ThreeNode? && key < tree.pivota then
		QuerySubtree(tree.left, key)
	else if tree.ThreeNode? && key < tree.pivotb then
		QuerySubtree(tree.middle, key)
	else
		QuerySubtree(tree.right, key)
}

// function minElementOfSubtree(tree: Node) : int
// 	requires(OrderedTree(tree));
// 	ensures(forall x :: x in SubtreeContents(tree) ==> x >= minElementOfSubtree(tree));
// {
// 	if tree.Leaf? then tree.key
// 	else minElementOfSubtree(tree.left)
// }

// function maxElementOfSubtree(tree: Node) : int
// 	requires(OrderedTree(tree));
// 	ensures(forall x :: x in SubtreeContents(tree) ==> x <= maxElementOfSubtree(tree));
// {
// 	if tree.Leaf? then tree.key
// 	else maxElementOfSubtree(tree.right)
// }

datatype InsertionResult<Value> = InsertionResult(tree: Node<Value>, split: bool)
	
method InsertIntoSubtree<Value>(tree: Node<Value>, key: int, value: Value)
	returns (result: InsertionResult<Value>)
	requires TTSubtree(tree);
	ensures TTSubtree(result.tree);
	ensures SubtreeContents(result.tree) == SubtreeContents(tree)[key := value];
	ensures result.split ==> Height(result.tree) == Height(tree) + 1;
	ensures result.split ==> result.tree.TwoNode?;
	ensures !result.split ==> Height(result.tree) == Height(tree);
{
	if tree.Leaf? {
		if tree.key == key {
			result := InsertionResult(Leaf(key, value), false);
		} else if tree.key < key {
			var newright := Leaf(key, value);
			var newtree := TwoNode(tree, key, newright);
			assert(Height(newright) == Height(tree));
			assert(Height(newtree) == Height(tree) + 1);
			result := InsertionResult(newtree, true);
		} else {
			var newleft := Leaf(key, value);
			var newtree := TwoNode(newleft, tree.key, tree);
			assert(Height(newleft) == Height(tree));
			assert(Height(newtree) == Height(tree) + 1);
			result := InsertionResult(newtree, true);
		}
	} else if tree.TwoNode? {
		if key < tree.pivot {
			var subresult := InsertIntoSubtree(tree.left, key, value);
			if !subresult.split {
				result := InsertionResult(TwoNode(subresult.tree, tree.pivot, tree.right), false);
			} else {
				result := InsertionResult(ThreeNode(subresult.tree.left, subresult.tree.pivot,
					                                 subresult.tree.right, tree.pivot,
																					 tree.right), false);
			}
		} else {
			var subresult := InsertIntoSubtree(tree.right, key, value);
			if !subresult.split {
				result := InsertionResult(TwoNode(tree.left, tree.pivot, subresult.tree), false);
			} else {
				result := InsertionResult(ThreeNode(tree.left, tree.pivot,
			                		                  subresult.tree.left, subresult.tree.pivot,
																						subresult.tree.right), false);
			}
		}
	} else if tree.ThreeNode? {
		if key < tree.pivota {
			var subresult := InsertIntoSubtree(tree.left, key, value);
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
		} else if key < tree.pivotb {
			var subresult := InsertIntoSubtree(tree.middle, key, value);
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
			var subresult := InsertIntoSubtree(tree.right, key, value);
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

datatype Tree<Value> = EmptyTree | NonEmptyTree(root: Node<Value>)
		
predicate TTTree<Value>(tree: Tree<Value>) {
	tree.EmptyTree? || TTSubtree(tree.root)
}

function Contents<Value>(tree: Tree<Value>) : map<int, Value>
{
	if tree.EmptyTree?
		then map[]
	else
		SubtreeContents(tree.root)
}

function method Query<Value>(tree: Tree<Value>, key: int) : QueryResult<Value>
	requires(TTTree(tree));
  ensures Query(tree, key) == KeyDoesNotExist <==>
		(key !in Contents(tree));
  ensures Query(tree, key).ValueForKey? <==>
		(key in Contents(tree) && Contents(tree)[key] == Query(tree, key).value);
{
	if tree.EmptyTree? then
		KeyDoesNotExist
	else
		QuerySubtree(tree.root, key)
}

method Insert<Value>(tree: Tree<Value>, key: int, value: Value) returns (newtree: Tree<Value>)
	requires TTTree(tree);
	ensures TTTree(newtree);
	ensures Contents(newtree) == Contents(tree)[key := value];
	ensures newtree.NonEmptyTree?;
{
	if tree.EmptyTree? {
		newtree := NonEmptyTree(Leaf(key, value));
	} else {
		var result := InsertIntoSubtree(tree.root, key, value);
		newtree := NonEmptyTree(result.tree);
	}
}

// // datatype DeletionResult = DeletionResult(tree: Tree, merged: bool)
	
// // function DeleteFromSubtree(tree: Tree, key: int) : DeletionResult
// // 	requires TTTree(tree);
// // 	ensures TTTree(result.tree);
// // 	ensures Contents(result.tree) == Contents(tree) - {key};
// // {
// // 	if tree.EmptyTree? then
// // 		DeletionResult(EmptyTree, false)
// // 	else
// // 		match tree.root {
// // 			case Leaf(v) =>
// // 				if v == key then DeletionResult(EmptyTree, true)
// // 				else DeletionResult(tree, false)
// // 			case TwoNode(left, pivot, right) =>
// // 				if key < pivot then {
// // 					var subresult := DeleteFromSubtree(left, key);
// // 					if !subresult.merged then
// // 						DeletionResult(NonEmptyTree(subresult.root, tree.root.pivot, tree.root.right))
// // 					else
						
// // 				} else {
// // 				}
// // 		}
// // }

