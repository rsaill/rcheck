%{
open Utils
open Formula
open Syntax
open Syntax.P

let binOp_Expr a = BinOp_Expr(dloc,a)
let update_loc l = function
  | BinOp_Expr (_,op) -> BinOp_Expr (l,op)
  | x -> x
%}

%token EOF
%token THEORY
%token USERPASS
%token IS
%token END
%token <Syntax.P.loc*string> IDENT
%token <int> INTEGER
%token EQUALEQUAL
%token SEMICOLON
%token AND
%token IMPLY

%token RPAR
%token LPAR
%token LBRA
%token RBRA
%token LSQU
%token RSQU

%token OR
%token COMMA
%token PLUS
%token MINUS
%token STAR
%token DIV
%token MOD
%token POWER
%token MAPLET
%token DOTDOT
%token B_UNION
%token B_INTER
%token RELATION
%token DPRODUCT
%token RESTRICTION_D
%token SOUSTRACTION_D
%token RESTRICTION_CO
%token SOUSTRACTION_CO
%token SURCHARGE
%token PARTIELLE
%token TOTALE
%token P_INJECTION
%token T_INJECTION
%token S_PARTIELLE
%token S_TOTALE
%token B_TOTALE
%token B_PARTIELLE
%token EQUIV
%token EQUAL
%token NOT_EQUAL
%token MEMBER_OF
%token NOT_MEMBER_OF
%token INCLUDED
%token S_INCLUDED
%token NOT_INCLUDED
%token NOT_S_INCLUDED
%token SMALLER_OR_EQUAL
%token S_SMALLER
%token GREATER_OR_EQUAL
%token S_GREATER
%token SQUOTE
%token CIRC
%token INSERTION_T
%token INSERTION_Q
%token RESTRICTION_T
%token RESTRICTION_Q
%token AFFECTATION
%token PARALLEL
%token LSHIFT
%token RSHIFT
%token RPLUS
%token RMINUS
%token RMUL
%token RPOW
%token RDIV
%token BAR
%token RGE
%token RLE
%token RGT
%token RLT
%token ANTISLASH

%token TILDE

%token BANG
%token PERCENT
%token HASH
%token SIGMA
%token PI
%token SET
%token Q_UNION
%token Q_INTER
%token RSIGMA
%token RPI
%token DOT
 
%token EMPTY_SET
%token EMPTY_SEQ
%token QMARK

%token PBOOL
%token BTRUE
%token BFALSE
%token NOT

%start system
%type <Formula.r_theory list> system
%type <Formula.r_theory> theory 
%type <Formula.r_rule> rule
%type <Formula.formula> formula
%type <Formula.formula> c_formula
%type <Formula.formula> r_formula

/* 10 */
/* 20 */
%left SEMICOLON PARALLEL BAR
/* 30 */
%left IMPLY
/* 40 */
%left AND OR
/* 60 */
%left EQUIV
/* 110 */
/* 115 */
/* 120 */
/* 125 */
%left AFFECTATION
/* 160 */
%left INCLUDED S_INCLUDED EQUAL NOT_EQUAL MEMBER_OF NOT_INCLUDED NOT_MEMBER_OF S_SMALLER SMALLER_OR_EQUAL S_GREATER NOT_S_INCLUDED GREATER_OR_EQUAL ANTISLASH
%right COMMA
%left PARTIELLE S_PARTIELLE TOTALE S_TOTALE RELATION P_INJECTION T_INJECTION B_TOTALE B_PARTIELLE
%left B_INTER SURCHARGE SOUSTRACTION_D RESTRICTION_D DPRODUCT B_UNION MAPLET RESTRICTION_CO SOUSTRACTION_CO INSERTION_T RESTRICTION_T INSERTION_Q RESTRICTION_Q CIRC RLE RGE RGT RLT
/* 170 */
%left DOTDOT
/* 180 */
%left PLUS MINUS RPLUS RMINUS
/* 190 */
%left STAR DIV MOD LSHIFT RSHIFT RDIV RMUL
/* 200 */
%right POWER RPOW
/* 210 */
%nonassoc unary_minus
/* 220 */
/* 230 */
%left TILDE DOT
/* 250 */
%left LSQU LPAR
%left SQUOTE
%nonassoc RSQU
%%

system:
  EOF { [] }
| t=theory EOF { [t] }
| t=theory AND lst=system { t::lst }

theory:
  THEORY id=IDENT END { { tloc=$startpos; tname=snd id; trules=[] } }
| THEORY id=IDENT IS END { { tloc=$startpos; tname=snd id; trules=[] } }
| THEORY USERPASS { { tloc=$startpos; tname="userpass"; trules=[] } }
| THEORY id=IDENT IS lst=content END { { tloc=$startpos; tname=snd id; trules=lst } }

content:
  r=rule { [r] }
| r=rule SEMICOLON lst=content { r::lst }

rule:
  g=goal { ([],g) }
| hyps=hypotheses IMPLY g=goal_with_conj { (hyps,g) }

hypotheses:
  r=r_formula { [r] }
| r=r_formula AND lst=hypotheses { r::lst }

goal:
  fm=r_formula { Conclusion fm }
| f1=r_formula EQUALEQUAL f2=r_formula { Equation (f1,f2) }
| LPAR f1=formula EQUALEQUAL f2=formula RPAR { Equation (f1,f2) }

goal_with_conj:
  fm=conj_of_r_formulas { Conclusion fm }
| f1=conj_of_r_formulas EQUALEQUAL f2=conj_of_r_formulas { Equation (f1,f2) }
| LPAR f1=formula EQUALEQUAL f2=formula RPAR { Equation (f1,f2) }

conj_of_r_formulas:
  fm=r_formula { fm }
| f1=r_formula AND f2=conj_of_r_formulas { F_Binary ($startpos,BinOp_Prop Conjonction,f1,f2) }

c_formula:
  id=IDENT { F_Atom ($startpos,A_String (snd id)) }
| EMPTY_SET { F_Atom ($startpos,A_Empty_Set) }
| EMPTY_SEQ { F_Atom ($startpos,A_Empty_Seq) }
| QMARK { F_Atom ($startpos,A_Other) }
| BTRUE { F_Atom ($startpos,A_Btrue) }
| BFALSE { F_Atom ($startpos,A_Bfalse) }
| NOT LPAR fm=formula RPAR { F_Unary ($startpos,Not,fm) }
| PBOOL LPAR fm=formula RPAR { F_Unary ($startpos,Pbool,fm) }
| i=INTEGER { F_Atom ($startpos,A_Integer i) }
| LPAR fm=formula RPAR { F_Unary ($startpos,Par,fm) }
| LBRA fm=formula RBRA { F_Unary ($startpos,Bra,fm) }
| LSQU fm=formula RSQU { F_Unary ($startpos,Squ,fm) }
     (* Needed to parse SetOfRules.kernel.pmm *)
| LPAR formula RPAR IDENT { F_Atom ($startpos,A_Other) }
| LBRA formula RBRA IDENT { F_Atom ($startpos,A_Other) }
   
formula:
  fm=c_formula { fm }
| f1=formula op=infix_op f2=formula { F_Binary ($startpos,update_loc ($startpos(op)) op,f1,f2) }
| fm=formula tl=TILDE { tl;F_Unary ($startpos,Tilde $startpos(tl),fm) }
| MINUS fm=formula { F_Unary ($startpos,UMinus $startpos,fm) } %prec unary_minus
| f1=formula LPAR f2=formula RPAR { F_Binary($startpos,Application,f1,f2) }
| f1=formula LSQU f2=formula RSQU { F_Binary($startpos,Image,f1,f2) }
| LSQU f1=formula RSQU f2=formula { F_Binary($startpos,Substitution,f1,f2) }
| f1=formula AND f2=formula { F_Binary($startpos,BinOp_Prop Conjonction,f1,f2) }
| f1=formula IMPLY f2=formula { F_Binary($startpos,BinOp_Prop Implication,f1,f2) }
| f1=formula sm=SEMICOLON f2=formula { sm;F_Binary($startpos,BinOp_Expr ($startpos(sm),Composition),f1,f2) }
| bd=binder ids=ident_lst DOT fm=formula { F_Binder ($startpos,bd,(List.hd ids,List.tl ids),fm) }

r_formula:
  fm=c_formula { fm }
| f1=r_formula op=infix_op f2=r_formula { F_Binary($startpos,update_loc ($startpos(op)) op,f1,f2) }
| fm=r_formula tl=TILDE { tl; F_Unary ($startpos,Tilde $startpos(tl),fm) }
| MINUS fm=r_formula { F_Unary ($startpos,UMinus $startpos,fm) } %prec unary_minus
| f1=r_formula LPAR f2=formula RPAR { F_Binary($startpos,Application,f1,f2) }
| f1=r_formula LSQU f2=formula RSQU { F_Binary($startpos,Image,f1,f2) }
| LSQU f1=formula RSQU f2=r_formula { F_Binary($startpos,Substitution,f1,f2) }
| bd=binder ids=ident_lst DOT fm=r_formula { F_Binder ($startpos,bd,(List.hd ids,List.tl ids),fm) }

ident_lst_comma:
  id=IDENT { [id] }
| id=IDENT COMMA lst=ident_lst_comma { id::lst }

ident_lst:
  id=IDENT { [id] }
| LPAR lst=ident_lst_comma RPAR { lst }

%inline binder:
| PERCENT { Expr_B Lambda }
| SIGMA { Expr_B Sum }
| PI { Expr_B Prod }
| SET { Set }
| Q_UNION { Expr_B Q_Union }
| Q_INTER { Expr_B Q_Intersection }
| RSIGMA { Other_Binder }
| RPI { Other_Binder }
| BANG { Bang }
| HASH { Hash }

%inline infix_op:
  PLUS { binOp_Expr Addition }
| MINUS { binOp_Expr Difference }
| STAR { binOp_Expr Product }
| DIV { binOp_Expr Division }
| MOD { binOp_Expr Modulo }
| OR { BinOp_Prop Disjonction }
| POWER { binOp_Expr Power }
| MAPLET { Pair Maplet }
| COMMA { Pair Comma }
| DOTDOT { binOp_Expr Interval }
| B_UNION { binOp_Expr Union }
| B_INTER { binOp_Expr Intersection }
| RELATION { binOp_Expr Relations }
| DPRODUCT { binOp_Expr Direct_Product }
| RESTRICTION_D { binOp_Expr Domain_Restriction }
| SOUSTRACTION_D { binOp_Expr Domain_Soustraction }
| RESTRICTION_CO { binOp_Expr Codomain_Restriction }
| SOUSTRACTION_CO { binOp_Expr Codomain_Soustraction }
| SURCHARGE { binOp_Expr Surcharge }
| PARTIELLE { binOp_Expr (Functions Partial_Functions) }
| TOTALE { binOp_Expr (Functions Total_Functions) }
| P_INJECTION { binOp_Expr (Functions Partial_Injections) }
| T_INJECTION { binOp_Expr (Functions Total_Injections) }
| S_PARTIELLE { binOp_Expr (Functions Partial_Surjections) }
| S_TOTALE { binOp_Expr (Functions Total_Surjections) }
| B_TOTALE { binOp_Expr (Functions Bijections) }
| B_PARTIELLE { Other_Binary }
| EQUIV { BinOp_Prop Equivalence }
| EQUAL { BinOp_Pred Equality }
| NOT_EQUAL { BinOp_Pred Disequality }
| MEMBER_OF { BinOp_Pred Membership }
| NOT_MEMBER_OF { BinOp_Pred Non_Membership }
| INCLUDED { BinOp_Pred (Inclusion Not_Strict) }
| S_INCLUDED { BinOp_Pred (Inclusion Strict) }
| NOT_INCLUDED { BinOp_Pred (Inclusion Non_Inclusion) }
| NOT_S_INCLUDED { BinOp_Pred (Inclusion Non_Strict_Inclusion) }
| SMALLER_OR_EQUAL { BinOp_Pred (Inequality Smaller_or_Equal) }
| S_SMALLER { BinOp_Pred (Inequality Strictly_Smaller) }
| GREATER_OR_EQUAL { BinOp_Pred (Inequality Greater_or_Equal) }
| S_GREATER { BinOp_Pred (Inequality Strictly_Greater) }
| SQUOTE { Other_Binary }
| CIRC { binOp_Expr Concatenation }
| INSERTION_T { binOp_Expr Head_Insertion }
| INSERTION_Q { binOp_Expr Tail_Insertion }
| RESTRICTION_T { binOp_Expr Head_Restriction }
| RESTRICTION_Q { binOp_Expr Tail_Restriction }
| AFFECTATION { Affectation }
| PARALLEL { binOp_Expr Parallel_Product }
| LSHIFT { Other_Binary }
| RSHIFT { Other_Binary }
| RPLUS { Other_Binary }
| RMINUS { Other_Binary }
| RMUL { Other_Binary }
| RPOW { Other_Binary }
| RDIV { Other_Binary }
| RGE { Other_Binary }
| RLE { Other_Binary }
| RGT { Other_Binary }
| RLT { Other_Binary }
| BAR { Bar }
| ANTISLASH { Antislash }
| DOT { Other_Binary }

%%
