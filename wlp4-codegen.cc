#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <utility>
#include <fstream>
#include <sstream>
#include <deque>
#include <algorithm>
// #include "wlp4data.h"
#include "wlp4data.cc"

using namespace std;

int loopLabel = 0;
vector<int> labelVec;

// used to build the CFG (vector of rules)
struct rules {
    string lhs;
    vector <string> rhs;
    rules () {}
    rules(string lhsName, vector<string> rhsVec) {
        lhs = lhsName;
        if (rhsVec[0].find(".EMPTY") == string::npos) {rhs = rhsVec;}
        else {rhs = {};}
    }
    ~rules() {}
};

struct token {
    string kind;
    string lexeme;
    token() {}
    token(string kindVal, string lexemeVal) {
        kind = kindVal;
        lexeme = lexemeVal;
    }
};

struct slrDFA {
    map <pair<int, string>, int> transitions;
    map <pair<int, string>, int> reductions;

    slrDFA(map <pair<int, string>, int> transMap, map <pair<int, string>, int> redMap) {
        transitions = transMap; 
        reductions = redMap;
    }
};

struct Node {
  rules data;
  vector<Node*> children;
  token tokenIn;
  string type;
  Node(rules data) : data(data) {}
  Node(token tokenIn) : tokenIn(tokenIn) {}
  ~Node() {
    for( auto &c : children ) { delete c; }
  }
  Node* getChild(string name) {
    for (int i = 0; i < children.size(); i++) {
        if (children[i]->data.lhs == name) {
            return children[i];
        }
    }
    return nullptr;
  }
  Node* getChild(string name, int n) {
    for (int i = 0; i < children.size(); i++) {
        if (children[i]->data.lhs == name) {
            n -= 1;
            if (n == 0) {return children[i];}
        }
    }
    return nullptr;
  }

  void print(string prefix, ostream& out = cout) {
    out << prefix << data.lhs << ", " << type << endl;

    for (const auto& child : children) {
      for (int i = 0; i < prefix.length(); i++) {
        if (prefix[i] != '|') {prefix[i] = ' ';}
      }

      if (children.size() > 1) {
        if (child != children.front()) {
          prefix = prefix.substr(0, prefix.length()-2);
          if (child != children.back()) {prefix += "|-";}
          else {prefix += "'-";}
        } else {
          prefix += "|-";
        }
        child->print(prefix, out);
      } else {
        prefix += "'-";
        child->print(prefix, out);
      }
    }
  }
};

struct Variable {
    string name;
    string type;
    Variable(Node* tree) {
        if (tree->data.lhs == "dcl") {
            if (tree->children[0]->data.rhs.size() == 1) {type = "int";}
            else if (tree->children[0]->data.rhs.size() == 2) {type = "int*";}
            name = tree->children[1]->tokenIn.lexeme;
        }
    }
};

struct VariableTable {
    map<string, Variable> variableMap;
    void Add(Variable var) {
        if (variableMap.find(var.name) != variableMap.end()) {  // found
            throw runtime_error ("ERROR: duplicate procedure definition");
        } else {
            variableMap.insert(make_pair(var.name, var));
        }
    }
    Variable Get(string name) {
        if (variableMap.find(name) != variableMap.end()) {  // found
            return variableMap.at(name);
        } else {
            throw runtime_error ("ERROR: use of undeclared variable");
        }
    }
};

struct Procedure {
    string name;
    vector<string> signature;
    VariableTable localSymbolTable;
    void getParams(Node* node, vector<string> &lhsLeaf) {
        if (node->data.lhs == "type") {
            if (node->data.rhs.size() == 1) {lhsLeaf.push_back("int");}
            else if (node->data.rhs.size() == 2) {lhsLeaf.push_back("int*");}
        }
        for (Node* child : node->children) {getParams(child, lhsLeaf);}
    }
    void makeSymbolTable(Node* node, VariableTable &localSymbols) {
        if (node->data.lhs == "dcl") {
            localSymbols.Add(Variable(node));
        }
        for (Node* child : node->children) {makeSymbolTable(child, localSymbols);}
    }
    Procedure(Node* tree) {
        if (tree->data.lhs == "procedure") {
            name = tree->children[1]->tokenIn.lexeme;
            getParams(tree->children[3], signature);
            makeSymbolTable(tree->children[3], localSymbolTable); 
            makeSymbolTable(tree->children[6], localSymbolTable); 
        } else if (tree->data.lhs == "main") {
            name = "wain";
            getParams(tree->children[3], signature);
            getParams(tree->children[5], signature);
            makeSymbolTable(tree->children[3], localSymbolTable);
            makeSymbolTable(tree->children[5], localSymbolTable);
            makeSymbolTable(tree->children[8], localSymbolTable);
            if (signature[1] != "int") {throw runtime_error ("ERROR: type rule not satisfied");}
        }
    }
};

struct ProcedureTable {
    map<string, Procedure> procedureMap;
    void Add(Procedure var) {
        if (procedureMap.find(var.name) != procedureMap.end()) {  // found
            throw runtime_error ("ERROR: duplicate procedure definition");
        } else {
            procedureMap.insert(make_pair(var.name, var));
        }
    }
    Procedure Get(string name) {
        if (procedureMap.find(name) != procedureMap.end()) {  // found
            return procedureMap.at(name);
        } else {
            throw runtime_error ("ERROR: use of undeclared procedure");
        }
    }
};

void getArglist(Node* node, vector<string> &typeVec) {
    for (Node* child : node->children) {
        if (child->data.lhs == "arglist") {
            getArglist(child, typeVec);
        } else if (child->data.lhs == "expr") {
            typeVec.push_back(child->type);
        }
    }
}

// fill in the type field for all nonterminals that represent an expression (ie. expr, term, factor, lvalue)
// this function is called wrt a procedure and should have access to signature and symbol table for that proc
// start by looping over the children of the input tree and call annotateTypes on the children of the tree
void annotateTypes(Node* tree, Procedure &currentProc, ProcedureTable &procTable, Node* root) {
    // cout << tree->data.lhs << endl;

    if (tree->data.lhs == "factor") {
        if ((tree->data.rhs.size() == 1) && (tree->data.rhs[0] == "ID")) {
            tree->type = currentProc.localSymbolTable.Get(tree->children[0]->tokenIn.lexeme).type; 
        } else if (tree->data.rhs[0] == "NUM") {
            tree->type = "int";
        } else if (tree->data.rhs[0] == "NULL") {
            tree->type = "int*";
        }
    } else if (tree->data.lhs == "lvalue" && tree->data.rhs[0] == "ID") {
        tree->type = currentProc.localSymbolTable.Get(tree->children[0]->tokenIn.lexeme).type; 
    }
    
    // recurrsively set all types of children
    for (int i = 0; i < tree->children.size(); i++) {
        // annotateTypes(tree->children[i], currentProc, procTable, root);
        if (islower(tree->children[i]->data.lhs[0]) && tree->children[i]->type == "") {
            annotateTypes(tree->children[i], currentProc, procTable, root);
        }
    }
   
    // once children types have been set, determine the type of the current root
    if (tree->data.lhs == "factor") {
        if (tree->data.rhs[0] == "LPAREN") { // factor LPAREN expr RPAREN
            tree->type = tree->getChild("expr")->type;
        } else if (tree->data.rhs[0] == "AMP") { // factor AMP lvalue
            tree->type = "int*";
            if (tree->getChild("lvalue")->type != "int") {throw runtime_error ("ERROR: lvalue has wrong type");}
        } else if (tree->data.rhs[0] == "STAR") { // factor STAR factor
            tree->type = "int";
            if (tree->getChild("factor")->type != "int*") {throw runtime_error ("ERROR: factor has wrong type");}
        } else if (tree->data.rhs[0] == "NEW") { // factor NEW INT LBRACK expr RBRACK
            tree->type = "int*";
            if (tree->getChild("expr")->type != "int") {throw runtime_error ("ERROR: expr has wrong type");}
        } else if (tree->data.rhs[0] == "ID") {  // these are for procedure calls
            if (tree->data.rhs.size() > 1) {
                // check that the ID for the procedure does not match a variable name
                if (currentProc.localSymbolTable.variableMap.find(tree->children[0]->tokenIn.lexeme) == currentProc.localSymbolTable.variableMap.end()) {
                    // if its not a procedure throw an error
                    // if it is a procedure check that it has the right signature
                    if (procTable.procedureMap.find(tree->children[0]->tokenIn.lexeme) == procTable.procedureMap.end()) {
                        throw runtime_error ("ERROR: use of undeclared procedure");
                    } else {
                        if (tree->data.rhs[2] == "RPAREN") { // factor ID LPAREN RPAREN
                            // check the size of signature for the procedure being called (not the currentProc)
                            if (procTable.Get(tree->children[0]->tokenIn.lexeme).signature.size() > 0) {throw runtime_error ("ERROR: procedure should have no args");}
                        } else if (tree->data.rhs[2] == "arglist") { // factor ID LPAREN arglist RPAREN
                            vector<string> args;
                            getArglist(tree->getChild("arglist"), args);
                            if (args.size() == procTable.Get(tree->children[0]->tokenIn.lexeme).signature.size()) {
                                for (int i = 0; i < args.size(); i++) {
                                    if (args[i] != procTable.Get(tree->children[0]->tokenIn.lexeme).signature[i]) {
                                        throw runtime_error ("ERROR: args don't match function params");
                                    }
                                }
                            } else {throw runtime_error ("ERROR: num args don't match num of params for function");}
                        }
                    }
                } else {throw runtime_error ("ERROR: calling variable as function");}
                tree->type = "int";
            }
        }
    } else if (tree->data.lhs == "expr") {
        if (tree->data.rhs[0] == "expr") {
            if (tree->data.rhs[1] == "PLUS") {
                if ((tree->getChild("expr")->type == "int") && (tree->getChild("term")->type == "int")) {
                    tree->type = "int";
                } else if ((tree->getChild("expr")->type == "int*") && (tree->getChild("term")->type == "int")) {
                    tree->type = "int*";
                } else if ((tree->getChild("expr")->type == "int") && (tree->getChild("term")->type == "int*")) {
                    tree->type = "int*";
                } else {
                    throw runtime_error ("ERROR: can't add two pointers");
                }
            } else if (tree->data.rhs[1] == "MINUS") {
                if ((tree->getChild("expr")->type == "int") && (tree->getChild("term")->type == "int")) {
                    tree->type = "int";
                } else if ((tree->getChild("expr")->type == "int*") && (tree->getChild("term")->type == "int")) {
                    tree->type = "int*";
                } else if ((tree->getChild("expr")->type == "int*") && (tree->getChild("term")->type == "int*")) {
                    tree->type = "int";
                } else {
                    throw runtime_error ("ERROR: can't subtract a pointer from an int");
                }
            }
        } else {tree->type = tree->getChild("term")->type;}
    } else if (tree->data.lhs == "term") {
        tree->type = tree->getChild("factor")->type;
        if (tree->data.rhs[0] == "term") {
            if ((tree->getChild("term")->type != "int") && (tree->getChild("factor")->type != "int")) {
                throw runtime_error ("ERROR: types being multiplied/divided must be ints");
            }
        }
    } else if (tree->data.lhs == "lvalue") {
        if (tree->data.rhs[0] == "STAR") {
            tree->type = "int";
            if (tree->getChild("factor")->type != "int*") {throw runtime_error ("ERROR: factor has the wrong type");}
        } else if (tree->data.rhs[0] == "LPAREN") {
            tree->type = tree->getChild("lvalue")->type;
        }
    }
    
}

void checkStatementsTestDcls(Node* root, Procedure &newProc) {
    // cout << root->data.lhs << endl;
    if (root->data.lhs == "statement") {
        if (root->data.rhs[0] == "lvalue") {
            if (root->getChild("lvalue")->type != root->getChild("expr")->type) {throw runtime_error ("ERROR: type rule not satisfied");}
        } else if (root->data.rhs[0] == "PRINTLN") {
            if (root->getChild("expr")->type != "int") {throw runtime_error ("ERROR: type rule not satisfied");}
        } else if (root->data.rhs[0] == "DELETE") {
            if (root->getChild("expr")->type != "int*") {throw runtime_error ("ERROR: type rule not satisfied");}
        }
    } else if (root->data.lhs == "test") {
        if (root->getChild("expr", 1)->type != root->getChild("expr", 2)->type) {throw runtime_error ("ERROR: type rule not satisfied");}
    } else if (root->data.lhs == "dcls") {
        if (root->data.rhs.size() > 0) {
            if (root->data.rhs[0] == "dcls") {
                if (root->data.rhs[3] == "NUM") {
                    if (root->getChild("dcl")->children[0]->data.rhs.size() != 1) {throw runtime_error ("ERROR: type rule not satisfied");}
                } else if (root->data.rhs[3] == "NULL") {
                    if (root->getChild("dcl")->children[0]->data.rhs.size() != 2) {throw runtime_error ("ERROR: type rule not satisfied");}
                }
            }
        }
    }
    for (Node* child : root->children) {checkStatementsTestDcls(child, newProc);}
}

void collectProcedures(Node* root, ProcedureTable &procTable) {
    // cout << root->data.lhs << endl;
    if (root->data.lhs == "procedure" || root->data.lhs == "main") {
        Procedure newProc = Procedure(root);
        procTable.Add(newProc);
        annotateTypes(root, newProc, procTable, root);
        // root->print("", cout);
        checkStatementsTestDcls(root, newProc);
        if (root->getChild("expr")->type != "int") {
            throw runtime_error ("ERROR: type rule not satisfied");
        }
    }
    for (Node* child : root->children) {collectProcedures(child, procTable);}
}

void makeCFG (vector <rules> &CFG) {
    string input = WLP4_CFG;
    input.erase(0, 5);
    istringstream iss(input);
    string line;
    while (getline(iss, line)) {
        istringstream lineStream(line);
        rules rule;
        lineStream >> rule.lhs;
        string word;
        while (lineStream >> word) {
            if (word.find(".EMPTY") == string::npos) {rule.rhs.push_back(word);}
        }
        CFG.push_back(rule);
    }
}

void makeTransRedMaps (map <pair<int, string>, int> &transMap, map <pair<int, string>, int> &redMap) {
    int fromState, toState;
    string symbol, word, line;
    // making transitions map
    for (int i = 13; i < WLP4_TRANSITIONS.length(); i++) {
        if (WLP4_TRANSITIONS[i] == '\n') {
            word = "";
            for (int k = 0; k < 50; k++) {
                if (line[0] == ' ') {
                    fromState = stoi(word);
                    line.erase(0, 1);
                    break;
                }
                word += line[0];
                line.erase(0, 1);
            }
            word = "";
            for (int k = 0; k < 50; k++) {
                if (line[0] == ' ') {
                    symbol = word;
                    line.erase(0, 1);
                    break;
                }
                word += line[0];
                line.erase(0, 1);
            }
            word = "";
            for (int k = 0; k < line.length(); k++) {word += line[k];}
            toState = stoi(word);
            word = "";
            line = "";
            transMap[make_pair(fromState, symbol)] = toState;
        }
        line += WLP4_TRANSITIONS[i];
    }

    word = "";
    line = "";
    // making reductions map
    for (int i = 12; i < WLP4_REDUCTIONS.length(); i++) {
        if (WLP4_REDUCTIONS[i] == '\n') {
            word = "";
            for (int k = 0; k < 50; k++) {
                if (line[0] == ' ') {
                    fromState = stoi(word);
                    line.erase(0, 1);
                    break;
                }
                word += line[0];
                line.erase(0, 1);
            }
            word = "";
            for (int k = 0; k < 50; k++) {
                if (line[0] == ' ') {
                    toState = stoi(word);
                    line.erase(0, 1);
                    break;
                }
                word += line[0];
                line.erase(0, 1);
            }
            word = "";
            for (int k = 0; k < line.length(); k++) {word += line[k];}
            symbol = word;
            word = "";
            line = "";
            redMap[make_pair(fromState, symbol)] = toState;
        }
        line += WLP4_REDUCTIONS[i];
    }
}

void reduceTree(rules CFGrule, vector<Node*> &treeStack) {
    Node* newNode = new Node(CFGrule);   // new node storing CFG rule
    for (int i = 0; i < CFGrule.rhs.size(); i++) {
        newNode->children.insert(newNode->children.begin(), treeStack.back());  // copying the last len trees from the tree stack into the new node's children
        treeStack.pop_back();
    }
    treeStack.push_back(newNode);  // pushing new node onto tree stack
}

void reduceState(rules CFGrule, vector<int> &stateStack, slrDFA &dfa) {
    for (int i = 0; i < CFGrule.rhs.size(); i++) {stateStack.pop_back();}  // popping last len states from state stack
    pair<int, string> keyToFind = make_pair(stateStack.back(), CFGrule.lhs);
    int nextState = dfa.transitions.at(keyToFind);
    stateStack.push_back(nextState);  // pushing the next state corresponding to topmost state on state stack and the current symbol
}

void shift(deque<token> &inputSeq, vector<Node*> &treeStack, vector<int> &stateStack, slrDFA &dfa) {
    Node* unreadToken = new Node(inputSeq.front());  // new node corresponding to first token of unread input
    treeStack.push_back(unreadToken);
    pair<int, string> keyToFind = make_pair(stateStack.back(), inputSeq.front().kind);
    if (dfa.transitions.find(keyToFind) == dfa.transitions.end()) {  // transition not found
        for (auto i : treeStack ){
            delete i;
        }
        throw runtime_error ("ERROR: Transition not found");
    } else {
        stateStack.push_back(dfa.transitions.at(keyToFind));
    }
    inputSeq.pop_front();
}

// code generation

void findNonParams(Node* root, map<string, int> &offsetTable, int &varCount);
void computeArglist(Node *root, map<string, int> offsetTable, int &argCount);
void computeFactor(Node* root, map<string, int> &offsetTable);
void computeTerm(Node* root, map<string, int> &offsetTable);
void computeExpr(Node* root, map<string, int> &offsetTable);
void computeLvalue(Node* root, map<string, int> &offsetTable);
void computeTest(Node* root, map<string, int> &offsetTable);
void computeStatement(Node* root, map<string, int> &offsetTable);
void computeStatements(Node* root, map<string, int> &offsetTable);
void computeParamlist(Node* root, map<string, int> &newProcOffsetTable, int &paramCount);
void procCode(Node* root, map<string, int> &newProcOffsetTable);
void wainCode(Node* root, map<string, int> &offsetTable);
void procedures(Node* root, map<string, int> &offsetTable);

void Add(int d, int s, int t) { 
    cout << "add $" << d << ", $" << s << ", $" << t << "\n"; 
}
void Sub(int d, int s, int t) {
    cout << "sub $" << d << ", $" << s << ", $" << t << "\n";
}
void Mult(int s, int t) {
    cout << "mult $" << s << ", $" << t << "\n";
}
void Multu(int s, int t) {
    cout << "mult $" << s << ", $" << t << "\n";
}
void Div(int s, int t) {
    cout << "div $" << s << ", $" << t << "\n";
}
void Divu(int s, int t) {
    cout << "divu $" << s << ", $" << t << "\n";
}
void Mfhi(int d) {
    cout << "mfhi $" << d << "\n";
}
void Mflo(int d) {
    cout << "mflo $" << d << "\n";
}
void Lis(int d) {
    cout << "lis $" << d << "\n";
}
void Slt(int d, int s, int t) {
    cout << "slt $" << d << ", $" << s << ", $" << t << "\n";
}
void Sltu(int d, int s, int t) {
    cout << "sltu $" << d << ", $" << s << ", $" << t << "\n";
}
void Jr(int s) { 
    cout << "jr $"  << s << "\n"; 
}
void Jalr(int s) { 
    cout << "jalr $"  << s << "\n"; 
}
void Beq(int s, int t, string label) { 
    cout << "beq $" << s << ", $" << t << ", " + label + "\n"; 
}
void Bne(int s, int t, string label) { 
    cout << "bne $" << s << ", $" << t << ", " + label + "\n"; 
}
void Lw(int t, int i, int s) { 
    cout << "lw $" << t << ", " << i << "($" << s << ")" << "\n"; 
}
void Sw(int t, int i, int s) { 
    cout << "sw $" << t << ", " << i << "($" << s << ")" << "\n"; 
}
void Word(int i) {
  cout << ".word " << i << "\n";
}
void Word(string label) {
  cout << ".word " + label + "\n";
}
void label(string name) {
  cout << name + ":\n";
}
void push(int s) {
    cout << "sw $" << s << ", -4($30)" << endl;
    cout << "sub $30, $30, $4" << endl;
}
void pop(int d) {
    cout << "add $30, $30, $4" << endl;
    cout << "lw $" << d << ", -4($30)" << endl;
}
void pop() {
    cout << "add $30, $30, $4" << endl;
}
void constant(int t) {
    cout << "lis $3" << endl;
    cout << ".word " << t << endl;
}

void findNonParams(Node* root, map<string, int> &offsetTable, int &varCount) {
    if (root->data.lhs == "dcls" && root->children.size() == 5) {
        // varCount -= 1;
        findNonParams(root->getChild("dcls"), offsetTable, varCount);
        offsetTable.insert(make_pair(root->getChild("dcl")->children[1]->tokenIn.lexeme, varCount*4));
        // cout << "-------------- " << root->getChild("dcl")->children[1]->tokenIn.lexeme << ", " << varCount*4 << endl;
        varCount -= 1;
        if (root->children[3]->tokenIn.kind == "NUM") {
            constant(stoi(root->children[3]->tokenIn.lexeme));
        } else if (root->children[3]->tokenIn.kind == "NULL") {
            constant(1);
        }
        push(3);
    }
}

void computeArglist(Node *root, map<string, int> offsetTable, int &argCount) {
    if (root->children.size() == 1) {  // arglist expr
        computeExpr(root->getChild("expr"), offsetTable);
        push(3);
        argCount += 1;
    } else if (root->children.size() == 3) {  // arglist expr COMMA arglist
        computeExpr(root->getChild("expr"), offsetTable);
        push(3);
        argCount += 1;
        computeArglist(root->getChild("arglist"), offsetTable, argCount);
    }
}

void computeFactor(Node* root, map<string, int> &offsetTable) { // factor either returns a memory address or a value in $3
    int offset;
    // cout << "factor -> " << root->data.rhs[0] << root->data.rhs.size() << endl;
    if (root->children.size() == 1 && root->children[0]->tokenIn.kind == "ID") {
        offset = offsetTable.at(root->children[0]->tokenIn.lexeme);
        Lw(3, offset, 29);
    } else if (root->children.size() == 1 && root->children[0]->tokenIn.kind == "NUM") {
        constant(stoi(root->children[0]->tokenIn.lexeme));
    } else if (root->children.size() == 3 && root->children[0]->tokenIn.kind == "LPAREN") {
        computeExpr(root->getChild("expr"), offsetTable);
    } else if (root->children.size() == 1 && root->children[0]->tokenIn.kind == "NULL") {
        constant(1); // can't make this 0 because 0 is a multiple of 4 so it would be a valid address
    } else if (root->children.size() == 2 && root->children[0]->tokenIn.kind == "AMP") {
        // load the address of lvalue into $3
        computeLvalue(root->getChild("lvalue"), offsetTable);
    } else if (root->children.size() == 2 && root->children[0]->tokenIn.kind == "STAR") { // factor STAR factor
        // factor is a memory address - we want to store the value at this address into $3
        computeFactor(root->getChild("factor"), offsetTable);
        Lw(3, 0, 3);
    } else if (root->children.size() == 5 && root->children[0]->tokenIn.kind == "NEW") { // factor NEW INT LBRACK expr RBRACK
        loopLabel += 1;
        labelVec.push_back(loopLabel);
        computeExpr(root->getChild("expr"), offsetTable);
        push(1);
        Add(1, 3, 0);
        push(31);
        Lis(5);
        Word("new");
        Jalr(5);
        pop(31);
        pop(1);
        // if value returned in $3 = 0, then we change it to 1 to represent NULL
        Bne(3, 0, "notNull"+to_string(labelVec.back()));
        Lis(5);
        Word(1);
        Add(3, 5, 0);
        label("notNull"+to_string(labelVec.back()));
        labelVec.pop_back();
    } else if (root->children.size() == 3 && root->children[0]->tokenIn.kind == "ID") {  // factor ID LPAREN RPAREN
        push(31);
        push(29);
        Lis(5);
        Word("P"+root->children[0]->tokenIn.lexeme);
        Jalr(5);
        pop(29);
        pop(31);
    } else if (root->children.size() == 4 && root->children[0]->tokenIn.kind == "ID") {  // factor ID LPAREN arglist RPAREN
        int argCount = 0;
        push(31);
        push(29);
        computeArglist(root->getChild("arglist"), offsetTable, argCount);
        // cout << "---------" << root->children[0]->tokenIn.lexeme << "   argCount = " << argCount << endl;
        Lis(5);
        Word("P"+root->children[0]->tokenIn.lexeme);
        Jalr(5);
        for (int i = 0; i < argCount; i++) {pop();}
        pop(29);
        pop(31);
    }
    // for factor ID LPAREN RPAREN or for factor ID LPAREN arglist RPAREN
    // all registers are preserved by a call (including $31 and $29)
    // then caller pushes all arguments onto the stack
    // then calls procedure (new frame pointer gets set up here)
}

void computeTerm(Node* root, map<string, int> &offsetTable) {
    if (root->children.size() == 1) {
        // cout << "term -> factor" << endl;
        computeFactor(root->getChild("factor"), offsetTable);
    } else {
        computeTerm(root->getChild("term"), offsetTable);
        push(3);
        computeFactor(root->getChild("factor"), offsetTable);
        pop(5);
        if (root->children[1]->tokenIn.kind == "STAR") {
            Mult(5, 3);
            Mflo(3);
        } else if (root->children[1]->tokenIn.kind == "SLASH") {
            Div(5, 3);
            Mflo(3);
        } else if (root->children[1]->tokenIn.kind == "PCT") {
            Div(5, 3);
            Mfhi(3);
        }
    }
}

void computeExpr(Node* root, map<string, int> &offsetTable) {
    if (root->data.lhs == "expr" && root->children.size() == 1) {
        // cout << "expr -> term" << endl;
        computeTerm(root->getChild("term"), offsetTable);
    } else {
        computeExpr(root->getChild("expr"), offsetTable);
        push(3);
        computeTerm(root->getChild("term"), offsetTable);
        pop(5);
        if (root->children[1]->tokenIn.kind == "PLUS") {
            if (root->getChild("expr")->type == "int*" && root->getChild("term")->type == "int") {
                Mult(3, 4);
                Mflo(3);
                Add(3, 5, 3);
            } else if (root->getChild("expr")->type == "int" && root->getChild("term")->type == "int*") {
                Mult(5, 4);
                Mflo(5);
                Add(3, 5, 3);
            } else if (root->getChild("expr")->type == "int" && root->getChild("term")->type == "int") {
                Add(3, 5, 3);
            }
        } else if (root->children[1]->tokenIn.kind == "MINUS") {
            if (root->getChild("expr")->type == "int*" && root->getChild("term")->type == "int") {
                Mult(3, 4);
                Mflo(3);
                Sub(3, 5, 3);
            } else if (root->getChild("expr")->type == "int*" && root->getChild("term")->type == "int*") {
                Sub(3, 5, 3);
                Div(3, 4);
                Mflo(3);
            } else if (root->getChild("expr")->type == "int" && root->getChild("term")->type == "int") {
                Sub(3, 5, 3);
            }
        }
    }
}

void computeLvalue(Node* root, map<string, int> &offsetTable) {  // lvalue always returns a memory address in $3
    if (root->data.lhs == "lvalue" && root->children.size() == 1) { // ie. lvalue ID
        int offset = offsetTable.at(root->children[0]->tokenIn.lexeme);
        constant(offset);
        Add(3, 29, 3);
    } else if (root->data.lhs == "lvalue" && root->children.size() == 2) { // ie. lvalue STAR factor
        computeFactor(root->getChild("factor"), offsetTable);  // factor returns a variable of type int in $3
        push(3);
        // Add(3, 30, 0);
    } else if (root->data.lhs == "lvalue" && root->children.size() == 3) { // ie. lvalue LPAREN lvalue RPAREN
        computeLvalue(root->getChild("lvalue"), offsetTable);
    }
}

void computeTest(Node* root, map<string, int> &offsetTable) {
    if (root->children[1]->tokenIn.kind == "EQ") {
        computeExpr(root->getChild("expr", 1), offsetTable);
        push(3);
        computeExpr(root->getChild("expr", 2), offsetTable);
        pop(5);
        if (root->getChild("expr", 1)->type == "int*") {
            Sltu(7, 5, 3);
            Sltu(8, 3, 5);
        } else {
            Slt(7, 5, 3);
            Slt(8, 3, 5);
        }
        Bne(7, 8, "end"+to_string(labelVec.back()));  // if LT = GT then EQ
    } else if (root->children[1]->tokenIn.kind == "NE") {
        computeExpr(root->getChild("expr", 1), offsetTable);
        push(3);
        computeExpr(root->getChild("expr", 2), offsetTable);
        pop(5);
       if (root->getChild("expr", 1)->type == "int*") {
            Sltu(7, 5, 3);
            Sltu(8, 3, 5);
        } else {
            Slt(7, 5, 3);
            Slt(8, 3, 5);
        }
        Beq(7, 8, "end"+to_string(labelVec.back()));  // if LT != GT then NE
    } else if (root->children[1]->tokenIn.kind == "LT") {
        computeExpr(root->getChild("expr", 1), offsetTable);
        push(3);
        computeExpr(root->getChild("expr", 2), offsetTable);
        pop(5);
        if (root->getChild("expr", 1)->type == "int*") {Sltu(7, 5, 3);}
        else {Slt(7, 5, 3);}
        Beq(7, 0, "end"+to_string(labelVec.back()));
        // bne $7, $0, loop (ie. 7 = 1 which means expr1 ($5) < expr2 ($3))
    } else if (root->children[1]->tokenIn.kind == "LE") {
        computeExpr(root->getChild("expr", 1), offsetTable);
        push(3);
        computeExpr(root->getChild("expr", 2), offsetTable);
        pop(5);
        if (root->getChild("expr", 1)->type == "int*") {Sltu(7, 3, 5);}
        else {Slt(7, 3, 5);}
        Bne(7, 0, "end"+to_string(labelVec.back()));
        // beq $7, $0, loop (ie. 7 = 0 which means expr2 ($3) >= expr1 ($5))
    } else if (root->children[1]->tokenIn.kind == "GT") {
        computeExpr(root->getChild("expr", 1), offsetTable);
        push(3);
        computeExpr(root->getChild("expr", 2), offsetTable);
        pop(5);
        if (root->getChild("expr", 1)->type == "int*") {Sltu(7, 3, 5);}
        else {Slt(7, 3, 5);}
        Beq(7, 0, "end"+to_string(labelVec.back()));
        // bne $7, $0, loop (ie. 7 = 1 which means expr2 ($3) < expr1 ($5))
    } else if (root->children[1]->tokenIn.kind == "GE") {
        computeExpr(root->getChild("expr", 1), offsetTable);
        push(3);
        computeExpr(root->getChild("expr", 2), offsetTable);
        pop(5);
        Slt(7, 5, 3);
        Bne(7, 0, "end"+to_string(labelVec.back()));
        // beq $7, $0, loop (ie. 7 = 0 which means expr1 ($5) >= expr2 ($3))
    }
    Beq(0, 0, "loop"+to_string(labelVec.back()));
}

void computeStatement(Node* root, map<string, int> &offsetTable) {
    if (root->children[0]->data.lhs == "lvalue") {  // from indirect approach slides
        computeLvalue(root->getChild("lvalue"), offsetTable);
        push(3);
        computeExpr(root->getChild("expr"), offsetTable);
        pop(5);
        Sw(3, 0, 5);  // store the expr value into the address of lvalue
    } else if (root->children[0]->tokenIn.kind == "PRINTLN") {
        computeExpr(root->getChild("expr"), offsetTable);
        Add(1, 3, 0);
        push(31);
        push(29);
        Lis(5);
        Word("print");
        Jalr(5);
        pop(29);
        pop(31);
    } else if (root->children[0]->tokenIn.kind == "IF") {
        loopLabel += 2;
        labelVec.push_back(loopLabel);
        computeTest(root->getChild("test"), offsetTable);
        label("loop"+to_string(labelVec.back()));
        computeStatements(root->getChild("statements", 1), offsetTable);
        Beq(0, 0, "end"+to_string(labelVec.back()+1));
        label("end"+to_string(labelVec.back()));
        computeStatements(root->getChild("statements", 2), offsetTable);
        label("end"+to_string(labelVec.back()+1));
        labelVec.pop_back();
    } else if (root->children[0]->tokenIn.kind == "WHILE") {
        loopLabel += 1;
        labelVec.push_back(loopLabel);
        computeTest(root->getChild("test"), offsetTable);
        label("loop"+to_string(labelVec.back()));
        computeStatements(root->getChild("statements"), offsetTable);
        computeTest(root->getChild("test"), offsetTable); // check condition again
        label("end"+to_string(labelVec.back()));
        labelVec.pop_back();
    } else if (root->children[0]->tokenIn.kind == "DELETE") {
        loopLabel += 1;
        labelVec.push_back(loopLabel);
        computeExpr(root->getChild("expr"), offsetTable);
        Lis(5);
        Word(1);
        Beq(5, 3, "itsNull"+to_string(labelVec.back()));
        push(1);
        Add(1, 3, 0);
        push(31);
        Lis(5);
        Word("delete");
        Jalr(5);
        pop(31);
        pop(1);
        label("itsNull"+to_string(labelVec.back()));
        labelVec.pop_back();
    }
}

void computeStatements(Node* root, map<string, int> &offsetTable) {
    if (root->data.lhs == "statements" && root->children.size() == 2) {
        computeStatements(root->getChild("statements"), offsetTable);
        computeStatement(root->getChild("statement"), offsetTable);
    }
}

void computeParamlist(Node* root, map<string, int> &newProcOffsetTable, int &paramCount) {  // do not cout any pushing code here
    if (root->children.size() == 1) {  // paramlist dcl
        newProcOffsetTable.insert(make_pair(root->getChild("dcl")->children[1]->tokenIn.lexeme, (paramCount)*4));
        // cout << "----- " << root->getChild("dcl")->children[1]->tokenIn.lexeme << ", " << (paramCount)*4 << endl;
    } else if (root->children.size() == 3) {  // paramlist dcl COMMA paramlist
        computeParamlist(root->getChild("paramlist"), newProcOffsetTable, paramCount);
        paramCount += 1;
        newProcOffsetTable.insert(make_pair(root->getChild("dcl")->children[1]->tokenIn.lexeme, paramCount*4));
        // cout << "----- " << root->getChild("dcl")->children[1]->tokenIn.lexeme << ", " << paramCount*4 << endl;
    }
}

// procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE
void procCode(Node* root, map<string, int> &newProcOffsetTable) {
    label("P"+root->children[1]->tokenIn.lexeme);  // output the label name
    if (root->getChild("params")->children.size() != 0) {
        int paramCount = 1;
        computeParamlist(root->getChild("params")->getChild("paramlist"), newProcOffsetTable, paramCount);
    }
    int numParams = newProcOffsetTable.size();
    Sub(29, 30, 4);  // setting up FP
    int numNonParams = 0;
    findNonParams(root->getChild("dcls"), newProcOffsetTable, numNonParams);  // this will set up the SP
    computeStatements(root->getChild("statements"), newProcOffsetTable);
    computeExpr(root->getChild("expr"), newProcOffsetTable);
    for (int i = 0; i < newProcOffsetTable.size() - numParams; i++) {pop();} // pop all params and nonparams off the stack
    Jr(31);
}

// main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE
void wainCode(Node* root, map<string, int> &offsetTable) {
    if (root->data.lhs == "main") {
        offsetTable.insert(make_pair(root->getChild("dcl", 1)->children[1]->tokenIn.lexeme, 8));
        push(1); // what is in $1 and $2 at this point tho?
        offsetTable.insert(make_pair(root->getChild("dcl", 2)->children[1]->tokenIn.lexeme, 4));
        push(2);
        Sub(29, 30, 4); // set the frame pointer to be right above the top of current stack

        push(1);
        push(2);
        push(31);
        Lis(31);
        Word("init");
        if (root->getChild("dcl", 1)->getChild("type")->children.size() == 1) {Add(2, 0, 0);} // ie. first param is type INT
        Jalr(31);
        pop(31);
        pop(2);
        pop(1);

        int numNonParams = 0;
        findNonParams(root->getChild("dcls"), offsetTable, numNonParams);
        computeStatements(root->getChild("statements"), offsetTable);
        computeExpr(root->getChild("expr"), offsetTable);
        // Lw(3, 4, 29);
        for (int i = 0; i < offsetTable.size(); i++) {pop();} // pop all params and nonparams off the stack
        Jr(31);
    }
}

void procedures(Node* root, map<string, int> &offsetTable) {
    if (root->data.lhs == "procedures" && root->children.size() == 2) {
        procedures(root->getChild("procedures"), offsetTable);
        map<string, int> newProcOffsetTable;  // make new offset table everytime a procedure is made??
        procCode(root->getChild("procedure"), newProcOffsetTable);
    } else if (root->data.lhs == "procedures" && root->children[0]->data.lhs == "main") {wainCode(root->getChild("main"), offsetTable);}
    // for (Node* child : root->children) {wainCode(child, offsetTable);}
}

int main() {
    vector<rules> CFG;
    map <pair<int, string>, int> transMap; 
    map <pair<int, string>, int> redMap;
    string word;
    int index;
    deque<token> inputSeq;
    vector<int> stateStack = {0};
    vector<Node*> treeStack;

    makeCFG(CFG);
    makeTransRedMaps(transMap, redMap);
    slrDFA dfa = slrDFA(transMap, redMap); 

    // ifstream cin("program.asm");
    string line;
    while (getline(cin, line)) {
        istringstream iss(line);
        string word1, word2;
        if (iss >> word1 >> word2) {
            inputSeq.push_back(token(word1, word2));
        }
    }
    inputSeq.push_front(token("BOF", "BOF"));
    inputSeq.push_back(token("EOF", "EOF"));

    // P3
    pair<int, string> keyToFind;
    while (true) {
        keyToFind = make_pair(stateStack.back(), inputSeq.front().kind);
        while (dfa.reductions.find(keyToFind) != dfa.reductions.end()) {
            reduceTree(CFG[dfa.reductions.at(keyToFind)], treeStack);
            reduceState(CFG[dfa.reductions.at(keyToFind)], stateStack, dfa); 
            keyToFind = make_pair(stateStack.back(), inputSeq.front().kind);
        }
        try {shift(inputSeq, treeStack, stateStack, dfa);}
        catch(runtime_error &e) {
            cerr << e.what() << "\n";
            return 1;
        }
        if (treeStack.back()->tokenIn.kind == "EOF") {break;}
    }
    reduceTree(CFG[0], treeStack);

    ProcedureTable procTable;
    try {
        // P4
        collectProcedures(treeStack[0], procTable);
        // P5
        map<string, int> offsetTable;
        cout << ".import print" << endl << ".import init" << endl << ".import new" << endl << ".import delete" << endl;
        Lis(4);
        Word(4);
        procedures(treeStack[0]->getChild("procedures"), offsetTable);
    } catch(runtime_error &e) {
        cerr << e.what() << "\n";
        for (auto i : treeStack){
            delete i;
        }
        return 1;
    }

    delete treeStack.front();

    return 0;
}