/* References: 
Specification and Verification of object-oriented software, Rustan Leino.
Program Proofs book: Rustan Leino.
*/

class Node {
    var data: int
    var next: Node?

    ghost var tailContents: seq<int>
    ghost var footprint: set<object>

    ghost predicate valid()
        reads this, footprint
    {
        this in footprint &&
        (next != null ==> next in footprint && next.footprint <= footprint && 
            this !in next.footprint) &&
        (next == null ==> tailContents == []) &&
        (next != null ==> tailContents == [next.data] + next.tailContents)
    }

    constructor()
        modifies this
        ensures valid() && fresh(footprint - {this})
        ensures next == null
    {
        next := null;
        tailContents := [];
        footprint := {this};
    }
}

class Queue {
    var head: Node?
    var tail: Node?

    ghost var contents: seq<int>
    ghost var footprint: set<object>
    ghost var spine: set<Node>

    ghost predicate valid()
        reads this, footprint
    {
        this in footprint && spine <= footprint &&
        head != null && head in spine &&
        tail != null && tail in spine &&
        tail.next == null && 
        (forall n: Node? | n in spine :: n != null && n.footprint <= footprint && n.valid() && 
            (n.next == null ==> n == tail)) &&
        (forall n | n in spine :: n.next != null ==> n.next in spine) && 
        contents == head.tailContents
    }

    constructor()
        modifies this
        ensures valid() && fresh (footprint - {this})
        ensures |contents| == 0
    {
        var n := new Node();
        head := n; tail := n;
        contents := n.tailContents;
        footprint := {this} + n.footprint;
        spine := {n};
    }

    method front() returns (d: int)
        requires valid()
        requires 0 < |contents|
        ensures d == contents[0]
    {
        d := head.next.data;
    }

    method dequeue()
        requires valid()
        requires |contents| > 0
        modifies footprint
        ensures valid() && fresh(footprint - old(footprint))
        ensures contents == old(contents)[1..]
    {
        var n := head.next;
        head := n;
        contents := n.tailContents;
    }

    method enqueue(d: int)
        requires valid()
        modifies footprint
        ensures valid() && fresh(footprint - old(footprint))
        ensures contents == old(contents) + [d]
    {
        var n := new Node();
        n.data := d;
        tail.next := n;
        tail := n;

        forall m | m in spine {
            m.tailContents := m.tailContents + [d];
        }

        contents := head.tailContents;

        forall m | m in spine {
            m.footprint := m.footprint + n.footprint;
        }
        footprint := footprint + n.footprint;
        spine := spine + {n};
    }
}

method Driver() {
    var q := new Queue();

    q.enqueue(5);
    q.enqueue(6);
    q.enqueue(900);
    q.enqueue(100);
    q.enqueue(2143);
    // q.enqueue(431); // verification times out after this.

    var f := q.front();
    assert f == 5;

    q.dequeue();
    f := q.front();
    assert f == 6;

    q.dequeue();
    f := q.front();
    assert f == 900;

    q.dequeue();
    f := q.front();
    assert f == 100;

    q.dequeue();
    f := q.front();
    assert f == 2143;

    // q.dequeue();
    // f := q.front();
    // assert f == 143;
}