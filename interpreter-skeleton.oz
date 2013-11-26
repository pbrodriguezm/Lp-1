%%% Interpreter
%%%
%%% Last update: Wed Apr 7 2:30pm

% Concrete Syntax in the style of C++		Abstract Syntax Records
%======================================================================
% <s> :: = ';'								% skipStmt
%	| '{' <s1> { ';' <s2> } '}'				% seqStmt(S1 S2)
%											--See note below
%	| new <x> <s>							% newvarStmt(X S)
%											--ie. 'local'
%	| <x1> = <x2>							% vareqStmt(X1 X2)
%	| <x> = <v>								% valeqStmt(X V)
%	| if '(' <x> ')' <s1> else <s2>			% ifStmt(X S1 S2)
%	| <x>'(' <y1> { ',' <yn> } ')'			% fappStmt(X Ys)
%											% fprim(X Ys)
%
% NOTE: fappStmt and fprim have the same concrete syntax. The difference is
% that fappStmt is for user-defined functions and fprim is for built-in
% functions. For your project, this mean that if X is an identifier, then
% it's an fappStmt, but if it's one of 'cout' '+' '-' '*' '/' '==' etc.,
% then it's an fprim.
% ALSO, there can be more than two statements in a sequence. { <s1>;<s2>;<s3> }
% would be seqStmt(S1 seqStmt(S2 S3)).
%
%-----------------------------------------------------------------------------
% <v> :: = <int>								% <int>
%	| <bool>									% true | false
%	| 'anon(' <x1>...<xn> ')' '{' <s> '}'		% fdef(Xs S)
%
functor
import
	Application
	System
	Executionutils
	Utils
	
%declare
%[U] = {Module.link ['executionutils.ozf']}

% The module that contains the utils below.
% Needs to be located in the same directory as your
% other Oz files, and in the directory from which
% Oz is run. Alternatively, include a full path in
% the file name.

define

U=Executionutils
Show=System.showInfo


												% -----Stack Operations----------
MakeEmptyStack = Utils.makeEmptyStack				% proc {MakeEmptyStack ?OutStack}
StackIsEmpty = Utils.stackIsEmpty					% proc {StackIsEmpty InStack ?Bool}
PopSemStack = Utils.popSemStack						% proc {PopSemStack InStack ?Stmt#E|OutStack}
PushSemStack = Utils.pushSemStack					% proc {PushSemStack Stmt#E InStack ?OutStack}


												% -----Store Operations----------
NewLocnInStore = Utils.newLocnInStore				% proc {NewLocnInStore ?Locn}
LookupInStore = Utils.lookupInStore					% proc {LookupInStore Locn ?Value}
BindLocnValInStore = Utils.bindLocnValInStore		% proc {BindLocnValInStore Locn Val}
StoreContents = Utils.storeContents					% proc {StoreContents ?ListOfLocnValPairs}


												% -----Environment Operations----------
NewEnv = Utils.newEnv								% proc {NewEnv ?Env}
LookupInEnv = Utils.lookupInEnv						% proc {LookupInEnv Identifier Env ?StoreLocn}
RestrictE = Utils.restrictE							% proc {RestrictE Idents Env ?NewEnv}
AddMappingE = Utils.addMappingE						% proc {AddMappingE IdentLocnPairs Env ?NewEnv}
EnvContents = Utils.envContents						% proc {EnvContents Env ?ListofIdentLocnPairs}

% Three procedures to be written:
ExecuteProgram
ExecuteStatement
CreateVal

proc {ExecuteProgram Program}	% Calls ExecuteStatement with an initial semantic stack
%%% FILL IN %%%%%%%%%%%%%%%%%%%%%
	% You may pre-stock the store and environment with a handful of primitives like
	% cout and arithmetic operators. You can do this by creating a location in the store
	% for each (prefix) operator, adding the name of the prefix operator to that location
	% in the environment, and then binding the store location to the appropriate Oz procedure.
	% For example, to pre-stock cout:
	% local
	% L = {NewLocnInStore}
	% {BindLocnValInStore L Show}
	% E = {NewEnv}
	% NewE = {AddMappingE [cout#L] E} %Note: The #-sign creates a pair. It translates to a tuple having '#' as the label.

	local
		E = {NewEnv}
	
		L1 = {NewLocnInStore}
		{BindLocnValInStore L1 Show}

		L2 = {NewLocnInStore}
		{BindLocnValInStore L2 Number.'+'}

		L3 = {NewLocnInStore}
		{BindLocnValInStore L3 Number.'-'}

		L4 = {NewLocnInStore}
		{BindLocnValInStore L4 Number.'*'}
		
		L5 = {NewLocnInStore}
		{BindLocnValInStore L5 Value.'=='}
		
		L6 = {NewLocnInStore}
		{BindLocnValInStore L6 Int.'div'}
		
		Env = {AddMappingE [cout#L1 '+'#L2 '-'#L3 '*'#L4 '=='#L5 '/'#L6] E}
		
		S = {MakeEmptyStack}
		SF = {PushSemStack Program#Env S}
	in
		{Show "------------------------------------------------------"}
		{Show "Ejecutando"}
		{ExecuteStatement SF}
		{Show "Finalizado"}
	end
end

proc {ExecuteStatement Stack}	% Executes each kernel statement
%%% FILL IN %%%%%%%%%%%%%%%%%%%%%
	if {Not {StackIsEmpty Stack}} then
		
		local
			L
			NewEnv
			NewStack
			AuxStack
			Stmt#E|OutStack = {PopSemStack Stack}
			case Stmt
			of skipStmt then
				{Show " > skipStmt"}
				NewStack = OutStack
			[] fprim(X Ys) then
				Args = {Map Ys fun {$ Y} {LookupInStore {LookupInEnv Y E}} end} in
				{Show " > fprim"}
				{Procedure.apply {LookupInStore {LookupInEnv X E}} Args}
				NewStack = OutStack
			[] seqStmt(S1 S2) then 
	    			Stmt = {LookupInStor S1 S2} in 
	    			{PopSemStack S2 S1}
	    		
			[] newvarStmt(X S) then
			    	Stmt={LookupInStor S T} in
			    	{Remove T X}
			    
			[] vareqStmt(X1 X2) then
				Stmt = {Add Stmt X1} in
			    	{Add Stmt X1}
	    
			[] valeqStmt(X V) then
			[] ifStmt(X S1 S2) then
			
			[] fappStmt(X Ys) then
				Args={Map Ys fun {$ Y} {LookupInStore {LookupInEnv Y E}} end} in
				{Procedure.apply {LookupInStore {LookupInEnv X E}} Args}
			end
			% Recursive call to ExecuteStatement with new Stack (if non-empty)
		in
			{ExecuteStatement NewStack} 
		end
	end
end




%%%%



%% Abstract Syntax of Example programs.
%% ---YOU WILL NEED TO WRITE SOME ADDITIONAL ONES TO COMPLETELY TEST YOUR CODE
fun {NewStack}
   Stack={NewCell nil}
   proc {Push X} S in {Exchange Stack S X|S} end
   fun {Pop} X S in {Exchange Stack X|S S} X end
   in
      stack(push:Push pop:Pop)
end

fun {PopR S} case S of X|S1  then X#S1   end
end

fun {Reverse Xs}
   case Xs
   of nil then nil
   [] X|Xr then
      {Append {Reverse Xr} [X]}
end
end


fun {CreateVal V E}
   {Show "xxxxxxxxx"}
end
   
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

   fun {FreeVars St Dest}
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
	    T={SubtractList {AddList {FreeVars S Dest} Xs} Xs}
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

Program1 = newvarStmt('x' seqStmt(valeqStmt('x' false) seqStmt(ifStmt('x' skipStmt skipStmt) skipStmt)))
Program2 = newvarStmt('x' seqStmt(valeqStmt('x' 26) fprim(cout ['x'])))
%The following programs are from HW 4 Q# 5
P = newvarStmt('x' newvarStmt('y' seqStmt(valeqStmt('x' 3) vareqStmt('y' 'x'))))


P1 = newvarStmt('x'
			seqStmt(seqStmt(valeqStmt('x' 1)
					newvarStmt('x'
					seqStmt(valeqStmt('x' 2)
						fprim('cout' ['x']))))
				fprim('cout' ['x'])))
P2 = newvarStmt('Res'
			seqStmt(
				newvarStmt('Arg1'
					newvarStmt('Arg2'
						seqStmt(
							seqStmt(
								valeqStmt('Arg1' 7)
								valeqStmt('Arg2' 6))
							fprim('*' ['Arg1' 'Arg2' 'Res']))))
						fprim('cout' ['Res'])))
P3 = newvarStmt('X'
			newvarStmt('xtimesy'
			newvarStmt('tmp1'
					newvarStmt('tmp2'
							seqStmt(seqStmt(valeqStmt('X' 2)
									valeqStmt('xtimesy'
									fdef(['Y' 'Res']
											seqStmt(fprim('cout' ['Y']) fprim('*' ['X' 'Y' 'Res'])))))
								seqStmt(seqStmt(valeqStmt('tmp1' 3)
										fappStmt('xtimesy' ['tmp1' 'tmp2']))
									fprim('cout' ['tmp2'])))))))

								

{ExecuteProgram Program1} % Call to execute a program
{ExecuteProgram Program2}
{ExecuteProgram P}
{ExecuteProgram P1}
{ExecuteProgram P2}
{ExecuteProgram P3}

{Application.exit 0}
end

