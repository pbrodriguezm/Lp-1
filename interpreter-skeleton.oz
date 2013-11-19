%%%  Interpreter
%%%
%%%  Last update: Wed Apr 7 2:30pm

% Concrete Syntax in the style of C++                     Abstract Syntax Records
%================================================================================
% <s> ::= ';'                                             % skipStmt
%       | '{' <s1> { ';' <s2> } '}'                       % seqStmt(S1 S2)
%                                                              --See note below
%       | new <x> <s>                                     % newvarStmt(X S)
%                                                              --ie. 'local'
%       | <x1> = <x2>                                     % vareqStmt(X1 X2)
%       | <x> = <v>                                       % valeqStmt(X V)
%       | if '(' <x> ')' <s1> else <s2>                   % ifStmt(X S1 S2)
%       | <x>'(' <y1> { ',' <yn> } ')'                          % fappStmt(X Ys)
%                                                         % fprim(X Ys)
%
% NOTE: fappStmt and fprim have the same concrete syntax.  The difference is
% that fappStmt is for user-defined functions and fprim is for built-in 
% functions. For your project, this mean that if X is an identifier, then
% it's an fappStmt, but if it's one of 'cout' '+' '-' '*' '/' '==' etc.,
% then it's an fprim.
% ALSO, there can be more than two statements in a sequence. { <s1>;<s2>;<s3> }
% would be seqStmt(S1 seqStmt(S2 S3)). 
%
%-----------------------------------------------------------------------------
% <v> ::= <int>                                           % <int>
%       | <bool>                                          % true | false
%       | 'anon(' <x1>...<xn> ')' '{' <s> '}'             % fdef(Xs S)
%

declare
[U]={Module.link ['executionutils.ozf']}  % The module that contains the utils below.
                                          % Needs to be located in the same directory as your
                                          % other Oz files, and in the directory from which
                                          % Oz is run.  Alternatively, include a full path in
                                          % the file name.

                                        % -----Stack Operations----------
MakeEmptyStack=U.makeEmptyStack         % proc {MakeEmptyStack ?OutStack}
StackIsEmpty=U.stackIsEmpty             % proc {StackIsEmpty InStack ?Bool}
PopSemStack=U.popSemStack               % proc {PopSemStack InStack ?Stmt#E|OutStack}
PushSemStack=U.pushSemStack             % proc {PushSemStack Stmt#E InStack ?OutStack}

                                        % -----Store Operations----------
NewLocnInStore=U.newLocnInStore         % proc {NewLocnInStore ?Locn}
LookupInStore=U.lookupInStore           % proc {LookupInStore Locn ?Value}
BindLocnValInStore=U.bindLocnValInStore % proc {BindLocnValInStore Locn Val}
StoreContents=U.storeContents           % proc {StoreContents ?ListOfLocnValPairs}

                                        % -----Environment Operations----------
NewEnv=U.newEnv                         % proc {NewEnv ?Env}
LookupInEnv=U.lookupInEnv               % proc {LookupInEnv Identifier Env ?StoreLocn}
RestrictE=U.restrictE                   % proc {RestrictE Idents Env ?NewEnv}
AddMappingE=U.addMappingE               % proc {AddMappingE IdentLocnPairs Env ?NewEnv}
EnvContents=U.envContents               % proc {EnvContents Env ?ListofIdentLocnPairs}

% Three procedures to be written:
ExecuteProgram
ExecuteStatement
CreateVal

proc {ExecuteProgram Program}   % Calls ExecuteStatement with an initial semantic stack
%%% FILL IN %%%%%%%%%%%%%%%%%%%%%
   % You may pre-stock the store and environment with a handful of primitives like
   % cout and arithmetic operators.  You can do this by creating a location in the store
   % for each (prefix) operator, adding the name of the prefix operator to that location
   % in the environment, and then binding the store location to the appropriate Oz procedure.
   % For example, to pre-stock cout:
   % local
   % L={NewLocnInStore}
   % {BindLocnValInStore L Show}
   % E={NewEnv}
   % NewE={AddMappingE [cout#L] E}  %Note: The #-sign creates a pair.  It translates to a tuple having '#' as the label.
   local stack, myenv, MySemStat in
   stack = {MakeEmptyStack}
   myenv = {NewEnv}
   MySemStat = Program#myenv
   {ExecuteStatement {PushSemStack MySemStat stack}}
   end
   local  store myenv newE in
	store ={NewLocnInStore}
	{BindLocnValInStore L fprim}
	myenv={NewEnv}
	newE={NewEnv}
	newE={AddMappingE [cout#stack] myenv}
   end
 
end


proc {ExecuteStatement Stack}   % Executes each kernel statement
%%% FILL IN %%%%%%%%%%%%%%%%%%%%%
   % Check if stack is empty
   % If not, pop top statement off of the stack
   % Use a case statement to figure out which statement it is
   % Use the semantics defined in Section 2.4 of the textbook to execute
   % each statement. Each branch of the case should return the stack that
   % results from executing that statement.  The new stack will be passed as
   % the argument of the tail recursive call to ExecuteStatement.
   % Below are the semantics for built-in primitives defined for you.  (They have
   % the same concrete syntax as user-defined function calls, but the parser will figure
   % out which functions are defined by the user and which are built-in, and assign
   % different abstract syntax to each as appropriate.)
   % ****IMPLEMENTATION HINTS: *****
   % The store operations already handle the single-assignment semantics, so
   % you don't have to.
   % fappStmt: Consider using List.zip (see online Oz documentation); otherwise write your own
   %           recursive function to lookup actual args and pair them with formals.
   if {StackIsEmpty Stack} == false then
   local stmt env outstack in
      stmt#env|outstack = {PopSemStack stack}
      case %Stmt
      of fprim(X Ys) then
	 Args={Map Ys fun {$ Y} {LookupInStore {LookupInEnv Y E}} end} in
	 {Procedure.apply {LookupInStore {LookupInEnv X E}} Args} 
      %NewStack
      [] skipStmt then {executestatement outstack}
      end
   end
   % Recursive call to ExecuteStatement with new Stack (if non-empty)
end
Free
fun {CreateVal V E}             % Creates a value as defined by the BNF for <v> above
%%% FILL IN %%%%%%%%%%%%%%%%%%%%%
   % Construct the value specified by V and return it.
   % This is trivial for integers and booleans (the Oz function IsInt might be helpful),
   % but for procedures means constructing a pair containing
   % the procedure definition and the environment.
   % Don't forget that the contextual environment stored with the procedure should be
   % only the free identifiers used in the body of the procedure MINUS the formal parameters.
   % The utility {U.subtractList FreeIdents Formals} together with the Free procedure
   % defined below will make this easy to do.  
end

% The code below creates the procedure {Free Stmt} that returns a list of the identifiers
% that are free in Stmt.  It will be needed by CreateVal above in creating a procedure value.
% Be sure to take the time to look through this code and understand it.  It can be helpful as
% a model for ExecuteStatement, and you will be expected to understand it for the midterm exam.
local
   Remove = Record.subtract
   Add = fun{$ Fr X}
	    {AdjoinAt Fr X unit}
	 end
   AddList = fun{$ Fr Xs}
		{AdjoinList Fr {Map Xs fun{$ X} X#unit end}}
	     end
   SubtractList = fun{$ Fr Xs}
		     {FoldL Xs fun {$ X Y} {Record.subtract X Y} end Fr}
		end   

   fun {FreeVars St Dest} % Dest is a record of all free vars at "this" scope
      case St of skipStmt then Dest
      [] seqStmt(S1 S2) then
	 T={FreeVars S1 Dest} in 
	 {FreeVars S2 T}
      [] newvarStmt(X S) then
	 T={FreeVars S Dest} in
	 {Remove T X}
      [] vareqStmt(X1 X2) then
	 T={Add Dest X1} in
	 {Add T X2}
      [] valeqStmt(X V) then
	 T in 
	 case V of fdef(Xs S) then
	    T={U.subtractList {AddList {FreeVars S Dest} Xs} Xs}
	 else T=Dest end
	 {Add T X}
      [] ifStmt(X S1 S2) then
	 T1={Add Dest X}
	 T2={FreeVars S1 T1} in
	 {FreeVars S2 T2}
      [] fappStmt(X Ys) then
	 T={Add Dest X} in
	 {AddList T Ys}
      [] fprim(ExternalProcedure Args) then
	 {AddList Dest ExternalProcedure|Args}
      end
   end
in
   fun {Free St}
      Dest=freevars() in
      {Record.arity {FreeVars St Dest}}
   end
end



%% Abstract Syntax of Example programs.
%% ---YOU WILL NEED TO WRITE SOME ADDITIONAL ONES TO COMPLETELY TEST YOUR CODE
   Program1=skipStmt
%{ExecuteProgram Program1}
Program2=newvarStmt('x' seqStmt(valeqStmt('x' 3) fprim(cout ['x'])))
%The following programs are from HW 4 Q# 5
P1=newvarStmt('x'
	      seqStmt(seqStmt(valeqStmt('x' 1)
			      newvarStmt('x'
					 seqStmt(valeqStmt('x' 2)
						 fprim('cout' ['x']))))
		      fprim('cout' ['x'])))
P2a=newvarStmt('Res'
	       seqStmt(newvarStmt('Arg1'
				  newvarStmt('Arg2'
					     seqStmt(seqStmt(valeqStmt('Arg1' 7)
							     valeqStmt('Arg2' 6))
						     fprim('*' ['Arg1' 'Arg2' 'Res']))))
		       fprim('cout' ['Res'])))
P3=newvarStmt('X'
	      newvarStmt('xtimesy'
			 newvarStmt('tmp1'
				    newvarStmt('tmp2'
					       seqStmt(seqStmt(valeqStmt('X' 2)
							       valeqStmt('xtimesy'
									 fdef(['Y' 'Res']
									      fprim('*' ['X' 'Y' 'Res']))))
						       seqStmt(seqStmt(valeqStmt('tmp1' 3)
								       fappStmt('xtimesy' ['tmp1' 'tmp2']))
							       fprim('cout' ['tmp2'])))))))
						       
in {ExecuteProgram Program2} % Call to execute a program

