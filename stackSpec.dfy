/* https://dafny.org/blog/2023/08/14/clear-specification-and-implementation/
*/

module StackSpecs {
    export
        provides StackModel, PushModel, PopModel, EmptyModel, IsEmptyModel
        provides PushPopVal, PushPopStack

    export Private
        provides StackModel, PushModel, PopModel, EmptyModel, IsEmptyModel
        provides PushPopVal, PushPopStack

    type StackModel<T> = seq<T>

    ghost predicate IsEmptyModel<T>(stk: StackModel<T>) {
        |stk| == 0
    }

    ghost function EmptyModel<T>() : StackModel<T>
        ensures (IsEmptyModel(EmptyModel<T>()))
    {
        []
    }

    ghost function PushModel<T>(stk: StackModel<T>, val : T) : StackModel<T>
        ensures !IsEmptyModel(PushModel(stk, val))
    {
        [val] + stk
    }

    ghost function PopModel<T>(stk: StackModel<T>) : (T, StackModel<T>)
        requires !IsEmptyModel(stk)
    {
        (stk[0], stk[1..])
    }

    lemma PushPopVal<T>(stk: StackModel<T>, val : T)
        ensures PopModel(PushModel(stk, val)).0 == val { /* empty function */ }
    
    lemma PushPopStack<T>(stk: StackModel<T>, val : T)
        ensures PopModel(PushModel(stk, val)).1 == stk { /* empty function */ }
}