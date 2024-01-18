include "StackSpec.dfy"

module LinkedStackImpl {
    import opened StackSpecs`Private

    class Stack<T> {
        var top: Node?<T>
        ghost var model: StackModel<T>
        ghost var footprint: set<object>

        ghost predicate ValidModel()
            reads this, top, footprint
        {
            this in footprint &&
            model == NodeModel(top) &&
            (top != null ==>
                top in footprint &&
                this !in top.footprint &&
                top.footprint <= footprint &&
                top.ValidModel()
            )
        }

        constructor()
            ensures ValidModel()
            ensures IsEmpty()
        {
            this.top := null;
            this.model := EmptyModel();
            this.footprint := {this};
        }

        predicate IsEmpty()
            reads this, top, footprint
            requires ValidModel()
            ensures IsEmpty() <==> IsEmptyModel(model)
        {
            top == null
        }

        method Push(val: T)
            requires ValidModel()
            modifies this
            ensures ValidModel()
            ensures !IsEmpty()
            ensures model == PushModel(old(model), val)
        {
            top := new Node<T>.InitNode(val, top);
            footprint := top.footprint + footprint;
            model := PushModel(model, val);
        }

        method Pop() returns (res: T)
            requires ValidModel()
            requires !IsEmpty()
            modifies this
            ensures ValidModel()
            ensures model == PopModel(old(model)).1
            ensures res == PopModel(old(model)).0
        {
            res := top.val;
            top := top.next;
            model := PopModel(model).1;
        }
    }

    class Node<T> {
        var val: T
        var next: Node?<T>

        ghost var model : StackModel<T>
        ghost var footprint : set<object>

        ghost predicate ValidModel()
            reads this, footprint
            decreases footprint + {this}
        {
            this in footprint &&
            (next == null ==> model == PushModel(EmptyModel(), val)) &&
            (next != null ==> (next in footprint &&
                                next.footprint <= footprint &&
                                this !in next.footprint &&
                                model == PushModel(next.model, val) &&
                                next.ValidModel()
                            ))
        }

        constructor InitNode (val: T, next: Node?<T>)
            requires next != null ==> next.ValidModel()
            ensures ValidModel()
            ensures model == PushModel(if next == null then EmptyModel()
                                else next.model, val)
            ensures next == null ==> footprint == {this}
            ensures next != null ==> footprint == {this} + next.footprint
        {
            this.val := val;
            this.next := next;
            this.model := PushModel(if next == null then EmptyModel()
                            else next.model, val);
            this.footprint := if next == null then {this} else {this} + next.footprint; 
        }

    }

    ghost function NodeModel<T>(node: Node?<T>) : StackModel<T>
        reads node
    {
        if node == null then EmptyModel() else node.model
    }
}