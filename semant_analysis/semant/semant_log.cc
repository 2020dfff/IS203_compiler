#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"

extern int semant_debug;
extern char *curr_filename;

static ostream& error_stream = cerr;
static int semant_errors = 0;

static Decl curr_decl = 0;
static bool has_return_bool = 0;
static int inloop = 0;
static int has_return_count = 0;

typedef SymbolTable<Symbol, Symbol> ObjectEnvironment; // name, type
ObjectEnvironment objectEnv;

typedef std::map<Symbol, CallDecl> CallTable;
CallTable callTable;

///////////////////////////////////////////////
// helper func
///////////////////////////////////////////////


static ostream& semant_error() {
    semant_errors++;
    return error_stream;
}

static ostream& semant_error(tree_node *t) {
    error_stream << t->get_line_number() << ": ";
    return semant_error();
}

static ostream& internal_error(int lineno) {
    error_stream << "FATAL:" << lineno << ": ";
    return error_stream;
}

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////

static Symbol
        Int,
        Float,
        String,
        Bool,
        Void,
        Main,
        print
;

bool isValidCallName(Symbol type) {
    return type != (Symbol)print;
}

bool isValidTypeName(Symbol type) {
    return type != Void;
}

//
// Initializing the predefined symbols.
//

static void initialize_constants(void) {
    // 4 basic types and Void type
    Bool        = idtable.add_string("Bool");
    Int         = idtable.add_string("Int");
    String      = idtable.add_string("String");
    Float       = idtable.add_string("Float");
    Void        = idtable.add_string("Void");
    // Main function
    Main        = idtable.add_string("main");

    // classical function to print things, so defined here for call.
    print        = idtable.add_string("printf");
}

/*
    TODO :
    you should fill the following function defines, so that semant() can realize a semantic
    analysis in a recursive way.
    Of course, you can add any other functions to help.
*/

static bool sameType(Symbol name1, Symbol name2) {
    return strcmp(name1->get_string(), name2->get_string()) == 0;
}

//???
static void install_calls(Decls decls) {
     for (int i=decls->first(); decls->more(i); i=decls->next(i)){
        Decl tmp_decl = decls->nth(i);
        Symbol name = tmp_decl->getName();
        Symbol type = tmp_decl->getType();
        if (tmp_decl->isCallDecl()){
            CallDecl call = static_cast<CallDecl>(tmp_decl);
            if (callTable[name] != NULL) {
                // no repeat function declaration
                semant_error(tmp_decl) << "Function " << name << " has been previously defined." << endl;
            }
            else if (sameType(name, print)){
                semant_error(tmp_decl) << "Function printf cannot be redefination." << endl;
            }
            else if (!isValidCallName(name)) {
                // function printf can't be defined twice
                semant_error(tmp_decl) << "Function printf cannot have a name as printf." << endl;
            }
            else if (type != Bool && type != Int && type != String && type !=  Float && type != Void) {
                // return type must be int,void,string,float,bool
                semant_error(tmp_decl) << "Function returnType error." << endl;
            }
            else {
                // update tables
                callTable[name] = call;
            }
        }
    }
    // int cnt = 0;
    // for (int i = decls->first(); decls->more(i); i = decls->next(i)) {
    //     Decl tmp_decl = decls->nth(i);
    //     if (tmp_decl->isCallDecl()) {
    //         CallDecl call = static_cast<CallDecl>(tmp_decl);
    //         if (strcmp(call->getName()->get_string(), "printf") == 0) {
    //             semant_error(tmp_decl) << "Function printf cannot be redefination.\n";
    //             semant_error(tmp_decl) << "Function printf cannot have a name as printf.\n";
    //         }
    //         else if (callTable.find(tmp_decl->getName()) != callTable.end())
    //             semant_error(tmp_decl) << "Function " << tmp_decl->getName() << " was previously defined.\n";
    //         else {
    //             callTable[tmp_decl->getName()] = call;
    //             cnt++;
    //         }
    //     }
    // }
    // if (semant_debug) cout << "Debug msg: Install " << cnt << "callDecls." << endl;
}

static void install_globalVars(Decls decls) {
     objectEnv.enterscope();

    for (int i=decls->first(); decls->more(i); i=decls->next(i)){
        Decl tmp_decl = decls->nth(i);
        if (!tmp_decl->isCallDecl()) {
            tmp_decl->check();
        }
    }
    // int cnt = 0;
    // for (int i = decls->first(); decls->more(i); i = decls->next(i)) {
    //     Decl tmp_decl = decls->nth(i);
    //     if (!tmp_decl->isCallDecl()) {
    //         VariableDecl variableDecl = static_cast<VariableDecl>(tmp_decl);
    //         if (objectEnv.lookup(variableDecl->getName()) != NULL)
    //             semant_error(variableDecl) << "var " << variableDecl->getName()->get_string() << " was previously defined.\n";
    //         else if (sameType(tmp_decl->getType(), Void)) {
    //             semant_error(tmp_decl) << "var " << tmp_decl->getName()->get_string() << " cannot be of type Void. Void can just be used as return type.\n";
    //         }
    //         else {
    //             objectEnv.addid(variableDecl->getName(), new Symbol(variableDecl->getType()));
    //             ++cnt;
    //         }
    //     }
    // }
    // if (semant_debug) {
    //     cout << "Debug msg: Install " << cnt << "globalVarDecls.\n" << endl;
    // }
}

static void check_calls(Decls decls) {
       for (int i=decls->first(); decls->more(i); i=decls->next(i)) {
        Decl tmp_decl = decls->nth(i);
        if (tmp_decl->isCallDecl()) {
            tmp_decl->check();
        }
    }
    // if (semant_debug) cout << "---check_calls---" << endl;
    // for (CallTable::iterator it = callTable.begin(); it != callTable.end(); it++) {
    //     it->second->check();
    // }
}

//done
static void check_main() {
    if (callTable.find(Main) == callTable.end()) {
        semant_error() << "Main function is not defined.\n";
        return;
    }
    else{
    curr_decl = callTable[Main];
    CallDecl main = static_cast<CallDecl>(curr_decl);
    if (main->getVariables()->len() > 0) {
        semant_error(curr_decl) << "Main function should not have any parameters.\n";
    }

    if (main->getType() != Void){
        semant_error(curr_decl) << "Main function should have return type Void.\n";
}
}
}

//almost done
void VariableDecl_class::check() {

    Symbol name = this->getName();
    Symbol type = this->getType();
    if (objectEnv.probe(name)) {
        semant_error(this) <<"variable" << name << " was previously defined." << endl;
    }
    else if (!isValidTypeName(type)) {
        semant_error(this) << "variable " << name << " cannot be of type Void. Void can just be used as return type." << endl;
    }
    else {
        objectEnv.addid(name, new Symbol(type));
    }

    //if (semant_debug) cout << "---VariableDecl_class---" << getName()->get_string() << endl;

    // if (objectEnv.probe(variable->getName()) != NULL)
    //     semant_error(this) << "variable " << variable->getName()->get_string() << " was previously defined.\n";
    // else if (!isValidTypeName(variable->getType()))
    //     semant_error(this) << "variable " << variable->getName()->get_string() << " cannot be of type Void. Void can just be used as return type.\n";
    // else
    //     objectEnv.addid(getName(), new Symbol(getType()));
}

//????
void CallDecl_class::check() {
    //if (semant_debug) cout << "---CallDecl_class::check---" << getName()->get_string() << endl;

    if (!isValidCallName(getType()))
        semant_error(this) << "ReturnType can not be print.\n";

    objectEnv.enterscope();
    Variables params = getVariables();

    for (int i = params->first(); params->more(i); i = params->next(i)) {
        Variable param = params->nth(i);
        if (semant_debug) cout << "---CallDecl_class---param_name---" << param->getName()->get_string() << endl;
        bool flag1 = true, flag2 = true;
        if (param->getType() == Void) {
            semant_error(this) << "Function " << getName()->get_string() << " 's parameter has an invalid type Void.\n";
            flag1 = false;
        }
        else if (objectEnv.probe(param->getName()) != NULL) {
            semant_error(this) << "Function " << getName()->get_string() << " 's parameter has a duplicate name " << param->getName() << ".\n";
            flag2 = false;
        }
        if (flag1 && flag2)
            objectEnv.addid(param->getName(), new Symbol(param->getType()));
    }

    getBody()->check(getType());

    //??????
    bool hasReturn = false;
    Stmts stmts = getBody()->getStmts();
    for (int i = stmts->first(); stmts->more(i); i = stmts->next(i)) {
        hasReturn = hasReturn ;
        // | stmts->nth(i)->isReturn();
        if (hasReturn) break;
    }
    if (!hasReturn)
        semant_error(this) << "Function " << getName()->get_string() << " must have an overall return statement.\n";

    objectEnv.exitscope();
}



void StmtBlock_class::check(Symbol type) {
     objectEnv.enterscope();
    has_return_count++;
    VariableDecls localVarDecls = this->getVariableDecls();
    for (int i=localVarDecls->first(); localVarDecls->more(i); i=localVarDecls->next(i)) {
        VariableDecl localVarDecl = localVarDecls->nth(i);
        localVarDecl->check();
    }

    Stmts localStmts = this->getStmts();
    for (int i=localStmts->first(); localStmts->more(i); i=localStmts->next(i)) {
        Stmt localStmt = localStmts->nth(i);
        localStmt->check(type);
    }
    has_return_count--;
    objectEnv.exitscope();
    
    // if (semant_debug) cout << "---StmtBlock_class::check---" << endl;
    // objectEnv.enterscope();
    // VariableDecls localVarDecls = getVariableDecls();
    // if (semant_debug) cout << "---StmtBlock_class::check---localVarDecl->getName()---" << " ";
    // for (int i = localVarDecls->first(); localVarDecls->more(i); i = localVarDecls->next(i)) {
    //     VariableDecl localVarDecl = localVarDecls->nth(i);
    //     if (semant_debug) cout << localVarDecl->getName()->get_string() << " ";
    //     localVarDecl->check();
    // }
    // if (semant_debug) cout << endl;
    // Stmts localStmts = getStmts();
    // if (semant_debug) cout << "---StmtBlock_class::check---localStmts->len()---" << localStmts->len() << endl;
    // Stmt localStmt;
    // for (int i = localStmts->first(); localStmts->more(i); i = localStmts->next(i)) {
    //     localStmt = localStmts->nth(i);
    //     localStmt->check(type);
    // }
    // objectEnv.exitscope();
}


//repeat*6
void IfStmt_class::check(Symbol type) {
    has_return_count++;
    Expr condition = this->getCondition();
    Symbol condType = condition->checkType();

    if (condType != Bool) {
        semant_error(this) << "Condition must be a Bool, got " << condType << '.' <<endl;
    }

    StmtBlock thenExpr = this->getThen();
    StmtBlock elseExpr = this->getElse();

    thenExpr->check(type);
    elseExpr->check(type);
    has_return_count--;
    // if (semant_debug) cout << "---IfStmt_class---" << endl;

    // Symbol conType = getCondition()->checkType();
    // if (!sameType(conType, Bool))
    //     semant_error(this) << "Condition must be a Bool, got " << conType->get_string() << ".\n";

    // getThen()->check(type);
    // getElse()->check(type);
}

void WhileStmt_class::check(Symbol type) {
    has_return_count++;
    inloop++;
    Expr condition = this->getCondition();
    Symbol condType = condition->checkType();

    if (condType != Bool) {
        semant_error(this) << "Condition must be a Bool, got " << condType << '.' <<endl;
    }

    StmtBlock body = this->getBody();
    body->check(type);
    inloop--;
    has_return_count--;
    // if (semant_debug) cout << "---WhileStmt_class---" << endl;

    // ++inloop;
    // if (semant_debug) cout << "while push inloop ,remaining " << inloop << endl;
    // Symbol conType = getCondition()->checkType();
    // if (!sameType(conType, Bool))
    //     semant_error(this) << "Condition must be a Bool, got " << conType->get_string() << ".\n";
    // getBody()->check(type);
    // --inloop;
    // if (semant_debug) cout << "while pop inloop ,remaining " << inloop << endl;
}

void ForStmt_class::check(Symbol type) {
     has_return_count++;
    inloop++;
    Expr init = this->getInit();
    Expr loop = this->getLoop();
    Expr condition = this->getCondition();

    init->checkType();
    loop->checkType();
    Symbol condType = condition->checkType();

    if(condType != Bool && !condition->is_empty_Expr()) {
        semant_error(this) << "Condition must be a Bool, got " << condType << '.' << endl;
    }

    StmtBlock body = this->getBody();
    body->check(type);
    inloop--;
    has_return_count--;
    // if (semant_debug) cout << "---ForStmt_class---" << endl;

    // ++inloop;
    // if (semant_debug) cout << "for push inloop ,remaining " << inloop << endl;
    // if (!getInit()->is_empty_Expr()) {
    //     getInit()->checkType();
    // }
    // if (!getLoop()->is_empty_Expr()) {
    //     getLoop()->checkType();
    // }
    // if (!getCondition()->is_empty_Expr()) {
    //     Symbol conType = getCondition()->checkType();
    //     if (!sameType(conType, Bool)) {
    //         semant_error(this) << "Condition must be a Bool, got " << conType->get_string() << ".\n";
    //     }
    // }
    // getBody()->check(type);
    // --inloop;
    // if (semant_debug) cout << "for pop inloop ,remaining " << inloop << endl;
}

void ReturnStmt_class::check(Symbol type) {
    if (has_return_count == 1){
        has_return_bool = 1;
    }

    Expr value = this->getValue();
    Symbol thisType = value->checkType();

    if (thisType != type) {
        semant_error(this) << "Returns " << thisType << " , but need " << type << endl;
    }
//     if (semant_debug) cout << "---ReturnStmt_class---" << endl;

//     Symbol thisType = this->getValue()->checkType();
//     if (!sameType(thisType, type))
//         semant_error(this) << "Returns " << thisType->get_string() << " , but need " << type->get_string() << ".\n";
}

void ContinueStmt_class::check(Symbol type) {
    if (semant_debug) cout << "---ContinueStmt_class---" << endl;

    if (inloop == 0)
        semant_error(this) << "continue must be used in a loop sentence.\n";
}

void BreakStmt_class::check(Symbol type) {

    if (semant_debug) cout << "---BreakStmt_class---" << endl;

    if (inloop == 0) {
        semant_error(this) << "break must be used in a loop sentence.\n";
    }
}



Symbol Call_class::checkType(){
     Symbol callName = this->getName();
    Actuals actuals = this->getActuals();
    Symbol result;

    if (!isValidCallName(callName)) {
        if (actuals->len()) {
            if (sameType(actuals->nth(actuals->first())->checkType(), String)) {
                for (int i=actuals->next(actuals->first()); actuals->more(i); i=actuals->next(i)) {
                    Symbol actualType = actuals->nth(i)->checkType();
                }
                setType(Void);
                result = Void;
            }
            else {
                semant_error(this) << "printf()'s first parameter must be of type String." << endl;
                result = Void;
            }
        }
        else {
            semant_error(this) << "printf() must has at last one parameter of type String." << endl;
        }
    }
    else {
        if (callTable.find(callName) == callTable.end()) {
            semant_error(this) << "Function " << callName << " has not been defined." << endl;
            setType(Void);
            result = Void;
        }
        else {
            CallDecl call = callTable[callName];
            Variables formals = call->getVariables();
            bool typeWrong = 0;
            int k = actuals->first();
            for (int i=formals->first(); formals->more(i); i=formals->next(i)) {
                if (!actuals->more(k)) {
                    semant_error(this) << "Function " << callName << " called with wrong number of arguments." << endl;
                    break;
                }
                Symbol actualType = actuals->nth(k)->checkType();
                Symbol formalType = formals->nth(i)->getType();
                if (actualType != formalType) {
                    semant_error(this) << "Function " << callName << ", the " << k+1 << " parameter should be " << formalType << " but provided a " << actualType << '.' <<endl;
                    typeWrong = 1;
                    break;
                }
                k = actuals->next(k);
            }
            if (!typeWrong && actuals->more(k)) {
                semant_error(this) << "Function " << callName << " called with wrong number of arguments." << endl;
            }
            Symbol callType = call->getType();
            setType(callType);
            result = callType;
        }
    }
    return result;
    // if (semant_debug) cout << "---Call_class---" << getName()->get_string() << endl;

    // if (callTable.find(getName()) == callTable.end()){
    //     if (strcmp(getName()->get_string(), print->get_string())==0) {
    //         Actuals actuals = getActuals();
    //         if (actuals->len() == 0) {
    //             semant_error(this) << "printf() must has at last one parameter of type String.\n";
    //         }
    //         else {
    //             for (int i = actuals->first(); actuals->more(i); i = actuals->next(i)){
    //                 Symbol actualType = actuals->nth(i)->checkType();
    //                 if (i == actuals->first()) {
    //                     if (!sameType(actualType, String))
    //                         semant_error(this) << "printf()'s first parameter must be of type String.\n";
    //                 }
    //             }
    //         }
    //         setType(Void);
    //         return Void;
    //     }
    //     semant_error(this) << "Function " << getName()->get_string() << " has not been defined.\n";
    //     setType(Void);
    //     return Void;
    // }

    // Variables variables1 = callTable[getName()]->getVariables();
    // Actuals actuals1 = getActuals();
    // if (variables1->len() != actuals1->len()) {
    //     semant_error(this) << "Function " << getName()->get_string() << " called with wrong number of arguments.\n";
    //     setType(callTable[getName()]->getType());
    //     return callTable[getName()]->getType();
    // }
    // for (int i = variables1->first(); variables1->more(i); i = variables1->next(i)) {
    //     if (variables1->nth(i)->getType() != actuals1->nth(i)->checkType())
    //         semant_error(this) << "Function " << getName()->get_string()<< " , the " << i+1 << " parameter should be " << variables1->nth(i)->getType()->get_string() << " but provided a " << actuals1->nth(i)->getType()->get_string() << ".\n";
    // }
    // if (semant_debug) cout << "---callTable[name]->getType():" << callTable[getName()]->getType()->get_string() << endl;
    // setType(callTable[getName()]->getType());
    // return callTable[getName()]->getType();
}

Symbol Actual_class::checkType(){
    if (semant_debug) cout << "---Actual_class---" << endl;

    Symbol type = expr->checkType();
    setType(type);
    return type;
}

Symbol Assign_class::checkType(){ // expr
 Symbol *expectType = objectEnv.lookup(this->lvalue);
    Symbol result;
    if (expectType) {
        Symbol actualType = this->value->checkType();
        if (sameType(actualType, *expectType)) {
            setType(*expectType);
        }
        else if (sameType(*expectType, Float) && sameType(actualType,Int)) {
            setType(Float);
        }
        else {
            semant_error(this) << "Right value must have type " << *expectType << " , got " << actualType << '.' <<endl;
        }
        result = this->type;
    }
    else {
        semant_error(this) << "Left value " << this->lvalue << " has not been defined." << endl;
        result = Void;
    }
    return result;
//     if (semant_debug) cout << "---Assign_class---" << lvalue->get_string() << endl;

//     if (objectEnv.lookup(lvalue) == NULL) {
//         semant_error(this) << "Left value " << lvalue << " has not been defined.\n";
//         return Void;
//     }

//     Symbol actualType = value->checkType();
//     Symbol expectedType = *(objectEnv.lookup(lvalue));
//     if (!sameType(expectedType, actualType)) {
//         semant_error(this) << "Right value must have type " << expectedType->get_string() << " , got " << actualType->get_string() << ".\n";
//     }
// //    if (sameType(expectedType, String)) {
// //        semant_error(this) << "Left value can not be String.\n";
// //    }
//     setType(expectedType);
//     return expectedType;
}



//repeat*19
Symbol Add_class::checkType(){ // +
    if (semant_debug) cout << "---Add_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot add a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Add_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else if (sameType(type1, Int) && sameType(type2, Int)) {
        if (semant_debug) cout << "---Add_class---type---Int" << endl;
        setType(Int);
        return Int;
    }
    else {
        if (semant_debug) cout << "---Add_class---type---Float" << endl;
        setType(Float);
        return Float;
    }
}

Symbol Minus_class::checkType(){ // -
    if (semant_debug) cout << "---Minus_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot minus a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Minus_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else if (sameType(type1, Int) && sameType(type2, Int)) {
        if (semant_debug) cout << "---Minus_class---type---Int" << endl;
        setType(Int);
        return Int;
    }
    else {
        if (semant_debug) cout << "---Minus_class---type---Float" << endl;
        setType(Float);
        return Float;
    }
}

Symbol Multi_class::checkType(){ // *
    if (semant_debug) cout << "---Multi_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot multi a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Multi_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else if (sameType(type1, Int) && sameType(type2, Int)) {
        if (semant_debug) cout << "---Multi_class---type---Int" << endl;
        setType(Int);
        return Int;
    }
    else {
        if (semant_debug) cout << "---Multi_class---type---Float" << endl;
        setType(Float);
        return Float;
    }
}

Symbol Divide_class::checkType(){ // /
    if (semant_debug) cout << "---Divide_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot div a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Divide_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else if (sameType(type1, Int) && sameType(type2, Int)) {
        if (semant_debug) cout << "---Divide_class---type---Int" << endl;
        setType(Int);
        return Int;
    }
    else {
        if (semant_debug) cout << "---Divide_class---type---Float" << endl;
        setType(Float);
        return Float;
    }
}

Symbol Mod_class::checkType(){ // %
    if (semant_debug) cout << "---Mod_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) || !sameType(type2, Int)) {
        semant_error(this) << "Cannot mod a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Mod_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Mod_class---type---Bool" << endl;
        setType(Int);
        return Int;
    }
}

Symbol Neg_class::checkType(){ // -
    if (semant_debug) cout << "---Neg_class---" << endl;

    Symbol type1 = e1->checkType();

    if (!sameType(type1, Int) && !sameType(type1, Float)) {
        semant_error(this) << "A " << type1->get_string() << " doesn't have a negative.\n";
        if (semant_debug) cout << "---Neg_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Neg_class---type---" << type1->get_string() << endl;
        setType(type1);
        return type1;
    }
}

Symbol Lt_class::checkType(){ // <
    if (semant_debug) cout << "---Lt_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Lt_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Lt_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Le_class::checkType(){ // <=
    if (semant_debug) cout << "---Le_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Le_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Le_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Equ_class::checkType(){ // ==
    if (semant_debug) cout << "---Equ_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((sameType(type1, Int) && !sameType(type2, Int) && !sameType(type2, Float)) ||
        (sameType(type1, Float) && !sameType(type2, Float) && !sameType(type2, Int)) ||
        (sameType(type1, Bool) && !sameType(type2, Bool)) ||
        sameType(type1, String)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Equ_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Equ_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}
//TODO:&&
Symbol Neq_class::checkType(){ // !=
    if (semant_debug) cout << "---Neq_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((sameType(type1, Int) && !sameType(type2, Int) && !sameType(type2, Float)) ||
        (sameType(type1, Float) && !sameType(type2, Float) && !sameType(type2, Int)) ||
        (sameType(type1, Bool) && !sameType(type2, Bool)) ||
        sameType(type1, String)) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Neq_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Neq_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Ge_class::checkType(){ // >=
    if (semant_debug) cout << "---Ge_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Ge_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Ge_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol Gt_class::checkType(){ // >
    if (semant_debug) cout << "---Gt_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if ((!sameType(type1, Int) && !sameType(type1, Float)) || (!sameType(type2, Int) && !sameType(type2, Float))) {
        semant_error(this) << "Cannot compare a " << type1->get_string() << " and a " << type2->get_string() << ".\n";
        if (semant_debug) cout << "---Gt_class---type---Void" << endl;
        setType(Void);
        return Void;
    }
    else {
        if (semant_debug) cout << "---Gt_class---type---Bool" << endl;
        setType(Bool);
        return Bool;
    }
}

Symbol And_class::checkType(){ // &&
    if (semant_debug) cout << "---And_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Bool) || !sameType(type2, Bool)) {
        semant_error(this) << "Cannot use && between " << type1->get_string() << " and " << type2->get_string() << ".\n";
        setType(Void);
        return Void;
    }
    else {
        setType(Bool);
        return Bool;
    }
}

Symbol Or_class::checkType(){ // ||
    if (semant_debug) cout << "---Or_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Bool) || !sameType(type2, Bool)) {
        semant_error(this) << "Cannot use || between " << type1->get_string() << " and " << type2->get_string() << ".\n";
        setType(Void);
        return Void;
    }
    else {
        setType(Bool);
        return Bool;
    }
}

Symbol Xor_class::checkType(){ // ^
    if (semant_debug) cout << "---Xor_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!(sameType(type1, Bool) && sameType(type2, Bool)) && !(sameType(type1, Int) && sameType(type2, Int))) {
        semant_error(this) << "Cannot use ^ between " << type1->get_string() << " and " << type2->get_string() << ".\n";
        setType(Void);
        return Void;
    }
    else if (sameType(type1, Bool)){
        setType(Bool);
        return Bool;
    }
    else {
        setType(Int);
        return Int;
    }
}

Symbol Not_class::checkType(){ // !
    if (semant_debug) cout << "---Not_class---" << endl;

    Symbol type1 = e1->checkType();
    if (!sameType(type1, Bool)) {
        semant_error(this) << "Cannot use ! upon " << type1->get_string() << ".\n";
        setType(Void);
        return Void;
    }
    else {
        setType(Bool);
        return Bool;
    }
}

Symbol Bitand_class::checkType(){ // &
    if (semant_debug) cout << "---Bitand_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) || !sameType(type2, Int)) {
        semant_error(this) << "Cannot use & between " << type1->get_string() << " and " << type2->get_string() << ".\n";
        setType(Void);
        return Void;
    }
    else {
        setType(Int);
        return Int;
    }
}

Symbol Bitor_class::checkType(){
    if (semant_debug) cout << "---Bitor_class---" << endl;

    Symbol type1 = e1->checkType();
    Symbol type2 = e2->checkType();

    if (!sameType(type1, Int) || !sameType(type2, Int)) {
        semant_error(this) << "Cannot use | between " << type1->get_string() << " and " << type2->get_string() << ".\n";
        setType(Void);
        return Void;
    }
    else {
        setType(Int);
        return Int;
    }
}

//bug*1 almost done
Symbol Bitnot_class::checkType(){
    if (semant_debug) cout << "---Bitnot_class---" << endl;

    Symbol type1 = this->e1->checkType();

    if (!sameType(type1, Int)) {
        //semant_error(this) << "Cannot use unary op ~ upon " << type1->get_string() << ".\n";
        setType(Int);
        //return Void;
    }
   else {
        semant_error(this) << "Cannot use unary not(~) upon " << type1 << '.' <<endl;
        setType(Void);
    }
    return this->type;
}




//repeat*4 done
Symbol Const_int_class::checkType(){
    setType(Int);
    return type;
}

Symbol Const_string_class::checkType(){
    setType(String);
    return type;
}

Symbol Const_float_class::checkType(){
    setType(Float);
    return type;
}

Symbol Const_bool_class::checkType(){
    setType(Bool);
    return type;
}

//??
Symbol Object_class::checkType(){
    if (semant_debug) cout << "---Object_class---" << var->get_string() << endl;

    if (!objectEnv.lookup(var)) {
        semant_error(this) << "object " << var->get_string() << " has not been defined.\n";
        setType(Void);
        return Void;
    }
    else {
        setType(*(objectEnv.lookup(var)));
        return *(objectEnv.lookup(var));
    }
}

//done
Symbol No_expr_class::checkType(){
    setType(Void);
    return getType();
}

//done
void Program_class::semant() {
   initialize_constants();
    install_calls(decls);
    check_main();
    install_globalVars(decls);
    check_calls(decls);
    
    if (semant_errors > 0) {
        cerr << "Compilation halted due to static semantic errors." << endl;
        exit(1);
    }
}



