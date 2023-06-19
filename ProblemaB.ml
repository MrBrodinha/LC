(* 47712, Emanuel Pacheco
   48160, Vicente Chã

Fontes Externas Usadas:
  - https://pt.wikipedia.org/wiki/Algoritmo_DPLL
  - https://en.wikipedia.org/wiki/DPLL_algorithm
  - http://www.diag.uniroma1.it/~liberato/ar/dpll/dpll.html
  - Próprio enunciado do trabalho

Comando para compilar
ocamlc -I f_parser/ f_parser.cma ProblemaB.ml -o PB
*)

open F_parser

(*--------------------------------------------------------------------------------------------------------------------------*)
(*
CNFC, NNFC, IMPFREE

Estás três funções convertem qualquer formula para NFC

Impfree -> remove implicações e equivalências
NNFC -> remove negações duplas, aplica leis de morgan
CNFC -> mete a fomrula no estilo (A | B | ...) & (Z | C | ...) usando distribuição
*)
let rec impfree form =
  match form with
  | Implies (a, b) -> impfree (Or (Not a, b))
  | Equiv (a, b) -> impfree (And (Implies(a,b), Implies(b,a)))
  | Not False -> True
  | Not True -> False
  | Not a -> Not (impfree a)
  | Or (a, b) -> Or (impfree a, impfree b)
  | And (a, b) -> And (impfree a, impfree b)
  | f -> f

let rec nnfc form =
  match form with
  | Not (Not a) -> nnfc a 
  | Not (Or (a, b)) -> nnfc (And (Not (a), Not (b)))
  | Not (And (a, b)) -> nnfc (Or (Not (a), Not (b)))
  | Not a -> Not (nnfc a)
  | Or (a, b) -> Or (nnfc a, nnfc b)
  | And (a, b) -> And (nnfc a, nnfc b)
  | f -> f

let rec cnfc form =
  let rec distr form1 form2 =
  match form1, form2 with
  | And (a, b), _ -> And (distr a form2, distr b form2)
  | _, And (a, b) -> And (distr form1 a, distr form1 b)
  | _ -> Or (form1, form2) in 

  match form with 
  | Or (a, b) -> distr (cnfc a) (cnfc b)
  | And (a, b) -> And (cnfc a, cnfc b)
  | form -> form
(*--------------------------------------------------------------------------------------------------------------------------*)

(*
Onde vai ser guardado as clausulas da formula, onde cada clasula é uma lista de literais em que cada literal é representado por "Xn" ou "!Xn"
*)
let lista_clausula = ref []

(*
Guarda uma string com as várias Var separadas por & ou |
Entre & são clausulas, entre | são literais

Por exemplo, a formula (a | b) & (c | d) seria guardada como "a|b&c|d"

casos extras que tratamos aqui também
Se verificamos que uma clausula só tem "False" enviamos logo uma lista vazia para dar UNSAT
Se verificamos que alguma clausula contem "True", podemos ignora la que devolve sempre True
Se verificamos que uma clausula contem False, filtramos a lista e removes o false
*)
let formula_to_list form =
  let rec clausulas_string form =
    match form with
    | Var a -> a
    | True -> "True"
    | False -> "False"
    | Not (Var a) -> "!"^a
    | Or (a, b) -> clausulas_string a ^"|"^clausulas_string b
    | And (a, b) -> clausulas_string a^"&"^clausulas_string b
    | _ -> "" in
  let string = clausulas_string form in
  let clausulas = String.split_on_char '&' string in
  
  for i = 0 to List.length clausulas - 1 do 
    let literais = String.split_on_char '|' (List.nth clausulas i) in
    if literais = ["False"] then lista_clausula := []::!lista_clausula
    else if List.mem "False" literais then lista_clausula := (List.filter (fun a -> a <> "False") literais)::!lista_clausula
    else if List.mem "True" literais then ()
    else lista_clausula := literais::!lista_clausula
  done

(*
Como trabalhamos com strings, precisamos de uma função extra para fazer o simetrico os valores
Caso tenhamos !Xn, o simetrico seria !!Xn que é equivalente a Xn
Caso tenhamos Xn, o simetrico seria !Xn
*)
let rec simetrico string =
if String.contains string '!' then String.sub string 1 (String.length string - 1)
else "!"^string

(*
Devolve as clausulas unitárias, ou seja as que só têm um literal     
*)
let rec unitaria clausulas = 
    match clausulas with
    | [] -> ""
    | x::xi -> match x with
      | [x] -> x
      | _ -> unitaria xi

(*
Simplifica as clausulas, ou seja, remove as clausulas que contenham o literal e remove o simetrico do literal das restantes clausulas
Por exemplo, {{−a, b, c}, {a}, {a, b, c}} e enviassemos "a" como literal ficaria {{b, c}}
*)
let simplificar literal clausulas =
  let temp_lista = ref [] in

  let rec remover_l lista acc =
    match lista with
    | [] -> acc
    | x::xi -> if x = (simetrico literal) then remover_l xi acc
      else remover_l xi (x::acc) in

  for i = 0 to List.length clausulas - 1 do
    if not (List.mem literal (List.nth clausulas i)) then
      temp_lista := (remover_l (List.nth clausulas i) [])::!temp_lista
  done;
  !temp_lista

(*
Converte uma 'a list list para uma 'a list
Ex. [[1;2];[3;4]] -> [1;2;3;4]
*)
let rec converter ll acc =
  match ll with
  | [] -> acc
  | x::xi -> converter xi (x@acc)

(*
Função que serve para procura do literal puro
Basicamente procuramos por um literal ou o simétrico que só apareça uma vez. 
Primeiro juntamos a lista de clausulas numa só lista e verificamos se existe algum literal (o seu positivo ou negativo)
que só aparece uma vez, se houver, devolvemos esse literal
*)
let rec literal_puro listas acc =
    match listas with 
    | [] -> ""
    | x::xi -> 
      if (List.mem x acc || List.mem (simetrico x) (acc@xi)) then literal_puro xi (x::acc)
      else x

(*
Se a lista de clausulas estiver vazia, devolvemos "SAT"
Caso haja alguma clausula vazia dentro da lista de clausulas, devolvemos "UNSAT"
Caso contrário, verificamos se há alguma clausula unitária, se houver, simplificamos a lista de clausulas, se não
verificamos se há algum literal puro, se houver, simplificamos a lista de clausulas, se não
escolhemos um literal qualquer e simplificamos a lista de clausulas com esse literal, se o resultado for "UNSAT" simplificamos a 
lista de clausulas com o simetrico desse literal, se não simplificamos a lista de clausulas com esse literal
*)
let rec dpll clausulas =
  if clausulas = [] then "SAT" 
  else if List.mem [] clausulas || List.mem ["False"] clausulas then "UNSAT" 
  else (
    let literal_unitario = unitaria clausulas in
    let puro = literal_puro (converter clausulas []) [] in
    if literal_unitario <> "" then dpll (simplificar literal_unitario clausulas)
    else if puro <> "" then dpll (simplificar puro clausulas)
    else (
      let primeiro = List.nth (List.nth clausulas 0) 0 in
      let next = dpll (simplificar (simetrico primeiro) clausulas) in
      if next <> "UNSAT" then dpll (simplificar primeiro clausulas)
      else next 
    )    
)

(*
main

Onde recebemos o input
Convertemos o input para uma formula
Convertemos a formula para ficar no tipo NFC
Convertemos a formula para uma lista de clausulas
Enviamos a lista de clausulas para o dpll e imprimimos o resultado
*)
let () =
  match parse "stdin" with
  | Some f -> (
    let nfc = cnfc (nnfc (impfree f)) in
    formula_to_list nfc;
    print_endline (dpll !lista_clausula)
  )
  | None -> ()

(*
Exemplos Input/Output:
(!X1 & (!X2 & !X3)) & ((!X2) <-> (X3 & (X2 & X1))) -> UNSAT
FALSE & TRUE -> UNSAT
TRUE | FALSE -> SAT
(!!(A | B) -> (C & !!B)) -> SAT
*)