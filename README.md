# 純粋関数型言語DIYUSI
## 概要
DIYUSIは，Martin-Löf型理論に基づく静的型システムを備えた純粋関数型言語です．
ヂユシと読みます．

## 文法

### トップレベル
ソースコードのトップレベルには以下を記述できます:
- 定数または関数の定義
- データ型の定義
- 項の型注釈
- 拡張構文の定義

定数cを自然数42として定義するには以下のように記述します:

    c := 42

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

### 項
項は以下の要素で構成されます:

- 識別子 (identifier)
- 型宇宙 (type universe)
- 関数適用 (function application)
- 中置記法 (infix notation)
- 依存関数型 (dependent function type)
- 非依存関数型 (non-dependent function type)
- 関数抽象 (function abstraction)
- 型注釈 (type annotation)
- let式 (let expression)
- case式 (case expression)
- 自然数リテラル natural number literal)
- 整数リテラル (integer literal)
- 文字列リテラル (string literal)
- タプル (tuple)
- 孔項 (hole)

#### 識別子 (Identifier)
識別子には，任意の英数文字列とアンダースコアを用いることができます．
また，末尾には任意個のプライム(`'`)を付けることができます．
他言語と異なり，識別子の先頭文字にも数字を用いることができます．
例: `x`, `f''`, `2DPoint`

#### 型宇宙 (Type Universe)
型宇宙とは，型に付けられる型のことあり，`Type`と記述します．
型宇宙には自然数による階層があり，階層を明記する場合，階層をnとすると`Type_n`のように記述します．

#### 関数適用 (Function Application)
関数`f`に引数`x`を適用するとき，`f x`のように記述します．
関数適用は左結合です．すなわち，`f a b`のように表記した場合，`(f a) b`のように結合するものとします．

#### 依存関数型 (Dependent Function Type)
依存関数型は，依存関数に付く型のことです．
依存関数とは，引数の値によって関数の値の型が変化するような関数のことです．
A型の引数xに依存して関数の値の型が`B`となる場合，そのような関数の型を`(x:A) -> B`のように記述します．ただし，`B`は`x`を含むことのできる項です．
依存関数型は中置記法`->`に関して右結合です．すなわち，

    (x:A) -> (y:B) -> C
    
のように表記した場合，

    (x:A) -> ((y:B) -> C)

のように結合するものとします．

#### 非依存関数型 (Non-Dependent Function Type)
非依存関数型は依存関数型の特殊な場合であり，引数の値によらず関数の値の型が一つに定まるような関数に付く型です．
`A`型の引数を受け取り，関数の値が引数の値によらず`B`型となるような関数の型は，`A -> B`のように記述されます．依存関数型と同様に，非依存関数型は中置記号`->`に関して右結合です．

#### 関数抽象 (function abstraction)
`A`型の値`x`を引数として，`t`を関数の値とするような関数は`\x:A -> t`と表記します．ただし，`t`は`x`を含むことのできる項です．型を省略して`\x -> t`と表記することもできます．

#### 型注釈 (type annotation)
DIYUSIの型システムにおいては型推論に理論的制限があるため，自動的な型付けができない項が存在します．そのような項に対して型注釈を与えることにより，コンパイラに型推論のヒントを提示することができます．
項`t`の型は`A`であるということを，`t:A`と表記します．
注意として，型注釈は構文の曖昧性のために依存関数型`(x:A) -> B`の丸括弧内に書くことはできません．

#### let式 (let expression)
let式はローカルスコープを作ることで局所的な定義を可能とします．
定義の記述を*def*とします．*def*の定義を利用することのできる項を*body*とします．以下のlet式は，*def*の定義を使った項*body*を表します:

    let def in body
    
例として，以下のlet式は10と評価されます:

    let x := 5; y := 2 in x + y

データ型の定義も可能です．ただし，局所的に定義されたデータ型の値を持ち出すことはできません．
以下のlet式はtrueと評価されます:
    
    let
        data Binary where
            zero : Binary
            one : Binary
        
        x := Binary::zero
    in
        x = Binary::zero

以下のlet式は無効です:
    
    let
        data Binary where
            zero : Binary
            one : Binary
        
        x := Binary::zero
    in
        Binary::zero

---

## 信号系 (signal system)
DIYUSIにおいて，副作用を伴う処理は信号系を用いて扱うことができます．
信号系では，時間によって変化する値を信号という概念で抽象化します．
信号間の関係を信号関数と呼ばれる関数で定めることにより，時間変化する対象を捉え，また変化のしかたをプログラマが決定することができます．

### 信号
信号には永久的・連続的に値をもつ連続時間信号と突発的・離散的に値をもつ離散時間信号が存在します．
信号種型`SigKind`は以下のように定義されます:

    data SigKind : Type -> Type where
        continuous : 'A -> SigKind A
        discrete : 'A -> SigKind A

`continuous`構築子により構築される信号種の値は，時間によって変化する`A`型の値を表現します．
`discrete`構築子により構築される信号種の値は，時間により突発的に発生する`A`型の値を表現します．
連続時間信号と離散時間信号はそれぞれ，リアクティブプログラミングにおけるBehaviorとEventの概念に酷似しています．

複数の信号をまとめた信号種は以下で定義されるSigVecKind型が付けられます:

    data SigVecKind n := Vec SigKind n

`SigVecKind`が含む信号種が全て連続時間信号種$S_1,S_2,\cdots,S_{n-1}$であるとき，そのような信号種はタプル型$S_1$×$S_2$×$\cdots$×$S_{n-1}$を値型とする信号種SigKind $S_1$×$S_2$×$\cdots$×$S_{n-1}$と同等であると考えることができます（ただし同値ではありません）．
