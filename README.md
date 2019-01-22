# 純粋関数型言語DIYUSI
## 概要
DIYUSIは，Martin-Löf型理論に基づく静的型システムを備えた純粋関数型言語です．
ヂユシと読みます．

### さまざまな例

自然数データ型Natは以下のようにして定義できます:

    data Nat : Type where
        zero : Nat
        succ : Nat -> Nat
    
自然数同士の加算を行う関数addは以下のように定義できます:

    add : Nat -> Nat -> Nat
    add m n := case m of
        Nat::zero => n
        Nat::succ k => Nat::succ (add k n)

二項演算子`+`を加算関数addとして定義するには以下のように記述します:

    infix + add

直積データ型Prodは以下のようにして定義できます:

    data Prod : Type -> Type -> Type where
        double : {'A,'B} -> A -> B -> Pred A B

直和データ型Unionは以下のようにして定義できます:

    data Union : Type -> Type -> Type where
        inl : {'A,'B} -> A -> Union A B
        inr : {'A,'B} -> B -> Union A B

長さ付き配列データ型Vecは以下のようにして定義できます:

    data Vec : Type -> Nat -> Type where
        empty : {A} -> Vec A 0
        cons : {A,n} -> A -> Vec A n -> Vec A (n+1)

真理値型Boolは以下のようにして定義できます:

    data Bool : Type where
        true : Bool
        false : Bool

条件分岐関数ifは以下のようにして定義できます:

    if : {'A} -> Bool -> A -> A -> A
    if predicate true_value false_value :=
        case predicate of
            Bool::true => true_value
            Bool::false => false_value

以上のものはすべて標準ライブラリ上で定義されています．

fizzbuzzの例:

    fizzbuzz : Nat -> String
    fizzbuzz n := (if (n%3=0) "fizz" "") ++ (if (n%5=0) "buzz" "")
    
    module
        use actor::proc::*
        use filesystem::stdout
        
        fizzbuzz_printer : Nat -> Proc
        fizzbuzz_printer n := proc [
            times (stdout `writeln $ fizzbuzz k) n
        ]
