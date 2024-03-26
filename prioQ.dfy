class Task {
    // var runningPrio: nat
    var queueingPrio: nat
    /* const core: nat */ // let's focus on single core systems for now
    const id: nat
    var next: Task?

    ghost var model: set<nat>
    ghost var footprint: set<object>

    ghost predicate valid()
        reads this, footprint
        decreases footprint + {this}
    {
        this in footprint &&
        (next != null ==> next in footprint &&
            next.footprint <= footprint &&
            this !in next.footprint &&
            next.valid() &&
            (forall y :: y in model ==> y <= queueingPrio)) &&
        (next == null ==> model == {queueingPrio}) &&
        (next != null ==> model == next.model + {queueingPrio})
    }

    constructor(p: nat, taskId: nat)
        ensures valid() && fresh(footprint - {this})
        ensures model == {p}
        ensures next == null
        ensures footprint == {this}
        ensures queueingPrio == p
    {
        queueingPrio := p;
        id := taskId;
        next := null;
        model := {p} ;
        footprint := {this};
    }
}

function OS_FindPrio(task: Task): nat
    reads task
{
    task.queueingPrio
}

class Queue {
    var head: Task?
    
    ghost var model: set<nat>
    ghost var footprint: set<object>

    ghost predicate valid()
        reads this, footprint
    {
        this in footprint && // self framing
        (head == null ==> model == {}) &&
        (head != null ==>
            head in footprint &&
            head.footprint <= footprint &&
            this !in head.footprint &&
            head.valid())
    }

    constructor() // create an empty list
        ensures valid()
        ensures model == {}
        ensures fresh(footprint - {this})
    {
        head := null;
        model := {};
        footprint := {this};
    }

    method recurse(task: Task?, p: nat, taskId: nat) returns (newTask: Task)
        requires task == null || task.valid()
        modifies if task != null then task.footprint else {}
        ensures newTask.valid()
        ensures task == null ==> fresh(newTask.footprint) && newTask.model == {p}
        ensures task != null ==> newTask.model == {p} + old(task.model)
        ensures task != null ==> fresh(newTask.footprint - old(task.footprint))
        decreases if task != null then task.footprint else {}
    {
        if task == null || (task != null && task.queueingPrio < p) {
            newTask := new Task(p, taskId);
            newTask.next := task;
            
            /* ***** GHOST UPDATES ***** */
            assert newTask.queueingPrio == p;
            if task != null {
                newTask.footprint := newTask.footprint + task.footprint;
                newTask.model := {p} + task.model;
            }

            assert newTask.next != null ==> forall y | y in newTask.next.model :: y < newTask.queueingPrio;
            assert newTask.valid();
        } else {
            assert task.next == null || task.next.valid();
            newTask := task;
            task.next := recurse(task.next, p, taskId);

            /* ***** GHOST UPDATES ***** */
            assert task.next.valid();
            assert task.queueingPrio >= task.next.queueingPrio;
            task.model := task.model + {p};
            assert forall y :: y in task.next.model ==> y <= task.queueingPrio;
            task.footprint := task.footprint + task.next.footprint;
            assert task.valid() && task.next.valid();
            assert newTask == head ==> head.valid();
        }
    }

    method enqueue(p: nat, taskId: nat)
        requires valid()
        requires taskId !in model
        modifies this, footprint // dynamic frame
        ensures valid() && fresh(footprint - old(footprint)) // swinging pivot restriction
        ensures model == old(model) + {taskId}
        ensures head != null
    {
        head := recurse(head, p, taskId);
        model := model + {taskId};
        footprint := head.footprint + {this};
    }

    method dequeue()
        requires head != null && valid()
        modifies this, footprint
        ensures valid() 
        ensures fresh(footprint - old(footprint))
        ensures head != null ==> model == old(model) - {old(head).id}
        ensures head == null ==> model == {}
    {
        var n := head;
        head := head.next;
        if head != null {
            model := model - {n.id};
        } else {
            model := {};
        }
    }

    method {:verify false} traverse(task: Task?)
    {
        if task != null {
            print OS_FindPrio(task), ", ", task.id, "\n";
            traverse(task.next);
        }
    }

    function front(): nat
        reads this, head
        requires head != null
    {
        head.id
    }  
}

method Main() {
    var q := new Queue();

    q.enqueue(10, 1);
    q.enqueue(20, 2);
    q.enqueue(30, 3);
    q.enqueue(5, 4);
    q.enqueue(1, 5);
    q.enqueue(2, 6);
    q.enqueue(30, 7);
    q.enqueue(15, 8);

    var f: nat := 0;

    if q.head != null {
        f := q.front();
        q.dequeue();
        print "HEAD NODE: ", f, "\n";
    }

    if q.head != null {
        f := q.front();
        q.dequeue();
        print "HEAD NODE: ", f, "\n";
    }

    if q.head != null {
        f := q.front();
        q.dequeue();
        print "HEAD NODE: ", f, "\n";
    }

    q.traverse(q.head);
}
