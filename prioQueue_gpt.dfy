class Node{
    var prio: nat
    var next: Node?

    /* ghost */ var footprint: set<object>

    /*ghost */ predicate valid()
        reads this, footprint
    {
        this in footprint &&
        (next != null ==> next in footprint && next.footprint < footprint && this !in next.footprint) &&
        (next != null ==> next.valid())
    }

    constructor()
        ensures fresh(footprint - {this})
        ensures next == null
    {
        next := null;
        footprint := {this};
    }

    predicate isPrevOf(n: Node)
        reads this
    {
        next == n
    }
}

class Queue{
    var head: Node?

    /* ghost */ var spine: seq<Node>
    /* ghost */ var footprint: set<object>

    /* ghost */ predicate valid()
        reads this, spine, footprint
    {
        (head == null ==> spine == []) &&
        (head != null ==> spine != [] && head == spine[0] &&
            (forall i | 0 <= i < |spine| - 1 :: spine[i] != null && spine[i].next == spine[i + 1]) &&
            (forall j | 0 <= j < |spine| :: spine[j] != null && spine[j].footprint <= footprint && spine[j].valid()) && 
            (forall k | 1 <= k < |spine| :: spine[k] != null ==> spine[k].next in spine && spine[k].next.valid()) &&
                spine[|spine| - 1].next == null)
    }

    constructor()
        ensures valid()
        ensures head == null && spine == []
        ensures footprint == {this}
    {
        // returns an empty queue
        head := null;
        spine := [];
        footprint := {this};
    }

    method enqueue(prio: nat, pos: nat)
        requires valid()
        requires 0 <= pos < |spine| - 1
        modifies this, footprint, spine
        ensures valid()
        ensures head != null
        ensures fresh(footprint - old(footprint))
        ensures |spine| == |old(spine)| + 1
    {
        var n := new Node();
        n.prio := prio;

        if(head == null) {
            head := n;
            spine := [head];
            head := spine[0];
            footprint := footprint + {head};
        } else {
            var curr := head;
            var newSpine := [head];
            assert curr in spine;
            assert head.footprint <= footprint;

            var i: nat := 0;
            footprint := footprint + n.footprint;

            while(i < pos && curr.next != null)
                invariant curr in spine
                invariant i < |spine|
                invariant curr != null
                invariant curr.footprint <= footprint
                decreases if curr != null then curr.footprint else {}
            {
                curr := curr.next;
                i := i + 1;
            }

            n.next := curr.next;
            curr.next := n;
            n.footprint := curr.footprint + n.footprint - {curr};
            assert n.valid();
            spine := spine[.. pos] + [n] + spine[pos ..];

            var j: int := 0;

            while(j < pos)
                invariant forall j :: 0 <= j < pos ==> spine[j] != null && spine[j].footprint <= footprint && spine[j].valid()
                decreases |spine| - j
            {
                spine[j].footprint := spine[j].footprint + n.footprint;
                j := j - 1;
            }
        }
    }
}

// method Driver() {
//     var q := new Queue();
//     q.enqueue(10, 0);
// }