%{
open Ast
open Lexing

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
/* general tokens */
%token EOF
%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token EQ       /* = */
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */

/* keyword */
%token <int64>  INT
%token NULL
%token <string> STRING
%token <string> IDENT
%token GLOBAL   /* global */
%token TBOOL /* bool */
%token TRUE /* true */
%token FALSE /* false */
%token FOR /* false */
%token NEW /* new */
%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token RETURN   /* return */
%token VAR      /* var */


/* bop */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token AND /* & */
%token OR /* |*/
%token BINAND /* [&] */
%token BINOR /* [|]*/
%token LT /* < */
%token GT /* > */
%token LTE /* <= */
%token GTE /*>= */
%token NEQ /* !=*/
%token LSL /* << */
%token LSR /* >> */
%token ASR /* >>> */

/* uop */
                /* - */
%token TILDE    /* ~ */
%token BANG     /* ! */



%token UNARYLEVEL /* Token only exists for precedence: not a real token */

/* precedence in oat pdf, see bop*/
%left BINOR
%left BINAND
%left OR
%left AND
%left EQEQ NEQ
%left LT LTE GT GTE
%left LSL LSR ASR
%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE
%nonassoc UNARYLEVEL
%nonassoc LBRACKET

/* ---------------------------------------------------------------------- */
/* Oat v1. syntax */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty

/* new type definitions*/
%type <Ast.exp Ast.node option> exp_opt
%type <Ast.stmt Ast.node option> stmt_opt
%type <Ast.exp Ast.node> gexp
%type <Ast.lhs Ast.node> lhs
%type <Ast.stmt Ast.node> if_stmt
%type <Ast.block> else_stmt
%type <Ast.vdecl> vdecl
%type <Ast.decl> decl
%type <(Ast.ty * string) list> arglist
%type <Ast.ty> arr_ty
%type <Ast.ty -> Ast.exp> arr_inner 

%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TINT   { TInt }
  | TBOOL  { TBool }
  | r=rtyp { TRef r } 


%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | EQEQ   { Eq } 
  | NEQ    { Neq } 
  | AND    { And}
  | OR     { Or } 
  | BINAND { IAnd } 
  | BINOR  { IOr } 
  | LT     { Lt } 
  | GT     { Gt } 
  | LTE    { Lte } 
  | GTE    { Gte } 
  | LSL    { Shl } 
  | LSR    { Shr } 
  | ASR    { Sar } 

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

gexp:
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | i=INT      { loc $startpos $endpos @@ CInt i } 
  | s=STRING   { loc $startpos $endpos @@ CStr s }
  | TRUE      { loc $startpos $endpos @@ CBool true } 
  | FALSE      { loc $startpos $endpos @@ CBool false } 
  | NEW t=arr_ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, gexp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }
lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | t=rtyp NULL           { loc $startpos $endpos @@ CNull t }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  |  u=uop e=exp %prec UNARYLEVEL
                        { loc $startpos $endpos @@ Uop (u, e) }
  | l=lhs               { loc $startpos $endpos @@ Lhs l }  
  | f=IDENT LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (f,es) }
  | LPAREN e=exp RPAREN { e } 
  /*new stuff*/
  | s=STRING   { loc $startpos $endpos @@ CStr s }
  | TRUE       { loc $startpos $endpos @@ CBool true } 
  | FALSE      { loc $startpos $endpos @@ CBool false } 
  | NEW t=arr_ty LBRACKET inner=arr_inner
               { loc $startpos $endpos @@ inner t }

arr_inner:
  | RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE
                                   { fun t -> CArr (t, es) }
  | e=exp RBRACKET                 { fun t -> NewArr (t, e) }
arr_ty:
  | TINT                           { TInt }
  | TBOOL                          { TBool }
  | TSTRING                        { TRef RString }
  | t=arr_ty LBRACKET RBRACKET     { TRef (RArray t) }

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

stmt: 
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | f=IDENT LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (f, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) } 
  | FOR LPAREN vd=separated_list(COMMA, vdecl) SEMI e=exp_opt 
                        SEMI s=stmt_opt RPAREN b=block
                        { loc $startpos $endpos @@ For(vd, e, s, b) } 

exp_opt:
  | (* empty *)       { None }
  | e=exp {Some e}
stmt_opt:
  | (* empty *)       { None }
  | s=stmt {Some s}
   

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
