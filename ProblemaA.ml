(* 47712, Emanuel Pacheco
   48160, Vicente Chã
  
Fontes Externas Usadas:
- Aula 4, 5, 6, 7 sobre Semântica da Lógica Proposicional
   
Comando para compilar -> ocamlopt -I f_parser/ f_parser.cmxa ProblemaA.ml*)
open F_parser


(*
  Variável onde vai ser guardado a letra lexicograficamente mais pequena, inicializada a "Z"
  caso não exista variáveis na fórmula   
*)
let z = ref "Z"

(*
  Função que vai converter a fórmula para portas NOR e para string

  Primeiro encontramos um "match form with" que é onde vai ser formada a string final e onde é também convertido
  tudo para NOR.

  Esta parte funciona de forma fácil, onde escrevemos manualmente as expressões para "Not", "And" e "Or" e chamamos
  os seus elementos de forma recursiva para formarem também.

  O implies poderia ter sido escrito de forma manual também, mas como o implies é equivalente a "!a | b", apenas chamamos
  esta fórmula de forma recursiva (dá para fazer isto nas fórmulas acima também, mas como queremos a forma minimal, mantemos
  as outras porque o implies devolve igual escrevendo manualmente ou "!a | b"). 

  O mesmo caso acontece no Equiv, onde poderiamos escrever manualmente, mas como ele equivale a "(A -> B) & (B -> A)", é mais fácil
  chamar esta fórmula de forma recursiva.

  CASOS ESPECIAIS:
  !(A | B) -> se chamassemos a função normalmente, está fórmula devolveria uma string maior do que a minimal, então tivemos de fazer
  um match dentro do "Not" no caso de ele seguir de um "Or", para devolver (A % B) em vez de uma string com o quadruplo do tamanho. 

  FALSE / TRUE -> Estas fórmulas não têm obrigatoriamente só uma fórmula, inicialmente escrevemos False como "A & !A" que devolve sempre falso,
  mas existe uma fórmula que ainda devolve algo mais pequeno, que no caso é o "!(A | !A)", que como falamos anteriormente, devolve uma string
  muito menor.

*)
let rec to_ns form =
  match form with
  | Var a -> if a < !z then z := a; a
  | Not a -> 
      (match a with
      | Or (a,b) -> "("^to_ns a^" % "^to_ns b^")"
      | _ -> "("^to_ns a^" % "^to_ns a^")")
  | And (a,b) -> "(("^(to_ns a)^" % "^(to_ns a)^") % ("^(to_ns b)^" % "^(to_ns b)^"))"
  | Or (a,b) -> "(("^(to_ns a)^" % "^(to_ns b)^") % ("^(to_ns a)^" % "^(to_ns b)^"))"
  | Implies (a,b) -> to_ns (Or(Not a, b))
  | Equiv (a,b) -> to_ns (And (Implies (a,b), Implies(b,a)))
  | False -> to_ns (Not(Or(Var !z, (Not (Var !z)))))
  | True -> to_ns (Not(False))


(*
  Este trecho de código é a secção principal do programa, responsável por chamar a função "to_ns" e imprimir o resultado no terminal.
*)
let () = 
 match parse "stdin" with
 | Some form -> (
  List.iter (fun f -> ()) form;
  List.iter (fun f -> (print_endline (to_ns f))) form;)
 | None -> ()

(*
Exemplos de inputs/outpus:
!(A | B) -> (A % B)
FALSE -> (Z % (Z % Z))
TRUE -> ((Z % (Z % Z)) % (Z % (Z % Z)))
!(FALSE | TRUE) -> ((Z % (Z % Z)) % ((Z % (Z % Z)) % (Z % (Z % Z))))
(FALSE | A) -> (((A % (A % A)) % A) % ((A % (A % A)) % A))
*)