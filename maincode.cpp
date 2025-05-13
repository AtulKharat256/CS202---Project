#include <iostream>
#include <fstream>
#include <regex>
#include <string>
#include <vector>
#include <sstream>    // ← add this at the top with your other includes


using namespace std;

int indentLevel = 0;

string getIndent() {
    if (indentLevel < 0) indentLevel = 0;
    return string(indentLevel * 4, ' ');
}


void parseExpression(const string& line) {
    smatch matches;
    // Track nested loops
    static vector<string> loopStack;

    static bool insideSwitch = false;
    static string switchVar;
    static vector<string> pendingCases;

    string trimmed = regex_replace(line, regex("^\\s+|\\s+$"), "");
    static bool insideIfElse = false;
    static bool insideStruct = false;
    static string currentStructName;
        static bool insideFunction = false;
    static bool sawIfReturn   = false;
    static string currentFunctionName;

        // ── 1) Skip C preprocessor directives ──────────────────────────────────
        if (!trimmed.empty() && trimmed[0] == '#') {
            return;
        }
    
// ── One-line “else return X;” after an if-return ──────────────────────
{
    static const regex else_return_val(R"(^else\s+return\s+([^;]+);)");
    if (insideIfElse && regex_search(trimmed, matches, else_return_val)) {
        // 1) emit the else-guard as a channel send + goto
        cout << getIndent()
             << ":: else   -> ret_" << currentFunctionName
             << " ! " << matches[1] << ";" << endl;
        cout << getIndent() << "goto end;" << endl;
        // 2) close the if…fi
        indentLevel--;
        cout << getIndent() << "fi;" << endl;
        insideIfElse = false;
        return;
    }
}

// ── One-line “else stmt;” after a  single-branch if ──────────────────
{
    static const regex else_stmt(R"(^else\s+(.+);)");
    if (insideIfElse && regex_search(trimmed, matches, else_stmt)) {
        cout << getIndent()
             << ":: else   -> " << matches[1] << ";" << endl;
        indentLevel--;
        cout << getIndent() << "fi;" << endl;
        insideIfElse = false;
        return;
    }
}




    // ── Combined “} else {” ───────────────────────────────────────────────
    {
        static const regex close_else(R"(\}\s*else\s*\{)");
        if (regex_search(trimmed, matches, close_else)) {
            // end the true‐branch and start the else‐branch
            indentLevel--;
            cout << getIndent() << ":: else ->" << endl;
            indentLevel++;
            return;
        }
    }


            // ── Inline “if(cond) continue;” ──────────────────────────────────────
    {
        static const regex if_cont_pat(R"(\s*if\s*\(\s*(.*?)\s*\)\s*continue\s*;)");
        if (regex_search(trimmed, matches, if_cont_pat)) {
            cout << getIndent() << "if" << endl;
            indentLevel++;
            cout << getIndent() << ":: (" << matches[1] << ") -> skip;" << endl;
            indentLevel--;
            cout << getIndent() << "fi;" << endl;
            return;
        }
    }
// ── Inline “if(cond) break; else stmt;” ─────────────────────────────────
{
    static const regex if_break_else_pat(
        R"(\s*if\s*\(\s*(.*?)\s*\)\s*break\s*;\s*else\s*(.+?);)"
    );
    if (regex_search(trimmed, matches, if_break_else_pat)) {
        cout << getIndent() << "if" << endl;
        indentLevel++;
        cout << getIndent()
             << ":: (" << matches[1] << ") -> break;" << endl;
        cout << getIndent()
             << ":: else   -> " << matches[2] << ";" << endl;
        indentLevel--;
        cout << getIndent() << "fi;" << endl;
        return;
    }
}




        // ── 2) Handle atomic blocks ───────────────────────────────────────────
    regex atomic_pat(R"(\s*atomic\s*\{)");
    if (regex_search(trimmed, matches, atomic_pat)) {
        cout << getIndent() << "atomic {" << endl;
        indentLevel++;
        return;
    }

 // ── 3) Handle typedef blocks ─────────────────────────────────────────
 regex td_pat(R"(\s*typedef\s+(\w+)\s*\{)");
 if (regex_search(trimmed, matches, td_pat)) {

    // record that we’re inside a typedef‐style struct
    currentStructName = matches[1];
    insideStruct = true;
    cout << getIndent()
         << "typedef " << currentStructName << " {"
         << endl;
    indentLevel++;
    return;
 }

    


    regex if_pattern(R"(\s*if\s*\(([^)]+)\)\s*\{)");
    regex else_pattern(R"(\s*else\s*\{)");
    regex while_pattern(R"(\s*while\s*\(\s*(.*?)\s*\)\s*\{)");
    regex for_pattern  (R"(\s*for\s*\(\s*(.*?);(.*?);(.*?)\s*\)\s*\{)");
    
    // Struct handling state
    
    regex switch_pattern(R"(\s*switch\s*\(\s*(\w+)\s*\)\s*\{)");
    regex case_pattern(R"(\s*case\s+(\d+)\s*:\s*)");
    regex default_pattern(R"(\s*default\s*:\s*)");

    if (regex_search(trimmed, matches, switch_pattern)) {
        switchVar = matches[1];
        cout << getIndent() << "if" << endl;
        indentLevel++;
        insideSwitch = true;
        pendingCases.clear();
        return;
    }

    if (regex_search(trimmed, matches, while_pattern)) {
        string cond = matches[1];
        bool isInfinite = (cond == "1" || cond == "true");

        // push either empty (infinite) or the real condition
        loopStack.push_back(isInfinite ? string() : cond);
 
        // open the do…od
        cout << getIndent() << "do" << endl;
        indentLevel++;

        // for finite loops, emit the entry‐guard
        if (!isInfinite) {
            cout << getIndent()
                 << ":: (" << cond << ") ->" << endl;
            indentLevel++;
        }
        return;
     }

     {
         static const regex inf_if_break(
             R"(\s*if\s*\(\s*(.*?)\)\s*break\s*;)"
         );
//-        if (!loopStack.empty() && loopStack.back().empty()
//-            && regex_search(trimmed, matches, inf_if_break)) {
//-            cout << getIndent()
//-                 << ":: (" << matches[1] << ") -> break" << endl;
//-            return;
//-        }
        if (!loopStack.empty() && loopStack.back().empty()
            && regex_search(trimmed, matches, inf_if_break))
       {
            cout << getIndent()
                 << ":: (" << matches[1] << ") -> break" << endl;
            return;
        }
     }
 
    // ── inside infinite loop: “else stmt;” becomes the else‐guard ──────────
//-    {
//-        static const regex inf_else(
//-            R"(\s*else\s*(.*?)\s*;)"
//-        );
//-        if (!loopStack.empty() && loopStack.back().empty()
//-            && regex_search(trimmed, matches, inf_else)) {
//-            cout << getIndent()
//-                 << ":: else   -> " << matches[1] << endl;
//-            return;
//-        }
//-    }
    if (!loopStack.empty() && loopStack.back().empty()) {
        // only emit a default guard for a “real” statement line ending in “;”
        static const regex stmt_pat(R"(^(.+?);$)");
        if (regex_search(trimmed, matches, stmt_pat)) {
            // remove any trailing “;” in the captured body
            string body = matches[1];
            cout << getIndent()
                 << ":: else -> " << body << ";" << endl;
            return;
        }
    }


// for(init; cond; iter) {
if (regex_search(trimmed, matches, for_pattern)) {
    // emit initializer
    cout << getIndent() << matches[1] << ";" << endl;
    loopStack.push_back(matches[3]);
    cout << getIndent() << "do\n";
    indentLevel++;
    cout << getIndent() << ":: (" << matches[2] << ") ->\n";
    indentLevel++;
    return;
}

    if (insideSwitch && regex_search(trimmed, matches, case_pattern)) {
        pendingCases.push_back(matches[1]);
        return;
    }

    if (insideSwitch && regex_search(trimmed, matches, default_pattern)) {
        if (!pendingCases.empty()) {
            // Flush pending cases before default
            cout << getIndent() << ":: (";
            for (size_t i = 0; i < pendingCases.size(); ++i) {
                if (i > 0) cout << " || ";
                cout << switchVar << " == " << pendingCases[i];
            }
            cout << ") ->" << endl;
            indentLevel++;
            pendingCases.clear();
        }
        if (insideSwitch) indentLevel--;
        cout << getIndent() << ":: else ->" << endl;
        indentLevel++;
        return;
    }

    // allow ++/-- on identifiers, array‐refs or struct‐fields
    regex inc_pattern(R"(([\w\[\]\.]+)\s*\+\+\s*;)");
    regex dec_pattern(R"(([\w\[\]\.]+)\s*--\s*;)");


    // ── Handle continue/break ───────────────────────────────────────────
regex continue_pattern(R"(\s*continue\s*;)");
if (regex_search(trimmed, matches, continue_pattern)) {
    cout << getIndent() << "skip;" << endl;
    return;
}
regex break_pattern(R"(\s*break\s*;)");
if (regex_search(trimmed, matches, break_pattern)) {
    cout << getIndent() << "break;" << endl;
    return;
}

    // Match a++;
    if (regex_search(trimmed, matches, inc_pattern)) {
        if (insideSwitch && !pendingCases.empty()) {
            cout << getIndent() << ":: (";
            for (size_t i = 0; i < pendingCases.size(); ++i) {
                if (i > 0) cout << " || ";
                cout << switchVar << " == " << pendingCases[i];
            }
            cout << ") ->" << endl;
            indentLevel++;
            pendingCases.clear();
        }

        string var = matches[1];
        cout << getIndent() << var << "++;" << endl;
        if (insideSwitch) indentLevel--;
        return;
    }


    // Match a--;
    if (regex_search(trimmed, matches, dec_pattern)) {
        if (insideSwitch && !pendingCases.empty()) {
            cout << getIndent() << ":: (";
            for (size_t i = 0; i < pendingCases.size(); ++i) {
                if (i > 0) cout << " || ";
                cout << switchVar << " == " << pendingCases[i];
            }
            cout << ") ->" << endl;
            indentLevel++;
            pendingCases.clear();
        }

        string var = matches[1];
        cout << getIndent() << var << "--;" << endl;
        if (insideSwitch) indentLevel--;
        return;
    }
    regex struct_start(R"(\s*struct\s+(\w+)\s*\{)");
    regex struct_field(R"(\s*(int|byte|short|bool)\s+(\w+)\s*;)");
    regex struct_end(R"(\s*\};)");
    regex struct_array_decl(R"(\s*struct\s+(\w+)\s+(\w+)\[(\d+)\];)");
    regex array_decl(R"((int|byte|short|bool)\s+(\w+)\[(\d+)\];)");

        // ── 12) struct‐pointer declarations ────────────────────────────────
    static const regex struct_ptr_decl(
        R"(\s*struct\s+(\w+)\s*\*\s*(\w+)\s*;)"
    );
    if (regex_search(trimmed, matches, struct_ptr_decl)) {
        // now we actually declare the pointer instead of stubbing it
        cout << getIndent()
             << matches[1] << "* " << matches[2] << ";"
             << endl;
        return;
    }

    // ── 13) pointer assignment & dereference ───────────────────────────
    static const regex ptr_assign(
        R"(\s*(\w+)\s*=\s*&?(\w+)(?:->(\w+)|\.(\w+))\s*;)"
    );
    if (regex_search(trimmed, matches, ptr_assign)) {
        // matches[1]=lhs, matches[2]=base, matches[3]=->field, matches[4]=.field
        string lhs   = matches[1];
        string base  = matches[2];
        string field = matches[3].matched ? matches[3].str()
                                          : matches[4].str();
        bool   isArrow = matches[3].matched;
        cout << getIndent()
             << lhs << " = "
             << (isArrow ? base + "->" + field
                         : base + "." + field)
             << ";"
             << endl;
        return;
    }



        // ── inline blocks ────────────────────────────────────────────────────
        regex inline_pat(R"(\s*inline\s+(\w+)\s*\(\s*(.*?)\s*\)\s*\{)");
        if (regex_search(trimmed, matches, inline_pat)) {
            cout << getIndent()
                 << "inline " << matches[1]
                 << "(" << matches[2] << ") {"
                 << endl;
            indentLevel++;
            return;
        }
    
        // Ternary conditional: a = (b > c) ? b : c;
    regex ternary_pattern(R"((\w+)\s*=\s*\(([^)]+)\)\s*\?\s*([^:]+)\s*:\s*(.+);)");
    if (regex_search(trimmed, matches, ternary_pattern)) {
        string lhs = matches[1];
        string condition = matches[2];
        string true_val = matches[3];
        string false_val = matches[4];

        cout << getIndent() << "if" << endl;
        indentLevel++;
        cout << getIndent() << ":: (" << condition << ") ->" << endl;
        indentLevel++;
        cout << getIndent() << lhs << " = " << true_val << ";" << endl;
        indentLevel--;  // End true branch

        cout << getIndent() << ":: else ->" << endl;
        indentLevel++;
        cout << getIndent() << lhs << " = " << false_val << ";" << endl;
        indentLevel--;  // End false branch

        indentLevel--;  // End if block
        cout << getIndent() << "fi" << endl;

        return;
    }


    if (regex_search(trimmed, matches, struct_start)) {
        currentStructName = matches[1];
        cout << getIndent() << "typedef " << currentStructName << " {" << endl;
        indentLevel++;
        insideStruct = true;
        return;
    }
    if (insideStruct && regex_search(trimmed, matches, struct_field)) {
        cout << getIndent() << matches[1] << " " << matches[2] << ";" << endl;
        return;
    }

        // ── support struct‐pointer fields as integer indices ───────────────────
    static const regex ptr_field(
        R"(\s*struct\s+(\w+)\s*\*\s*(\w+)\s*;)"
    );
    if (insideStruct && regex_search(trimmed, matches, ptr_field)) {
        // we represent every pointer as an index (int) into the object pool
        cout << getIndent()
             << "int " << matches[2] << ";" << endl;
        return;
    }

    // ── fall back to ordinary fields ───────────────────────────────────────
    if (insideStruct && regex_search(trimmed, matches, struct_field)) {
        cout << getIndent()
             << matches[1] << " " << matches[2] << ";" << endl;
        return;
    }

    // ── close typedef and emit memory‐model arrays ─────────────────────────
    if (insideStruct && regex_search(trimmed, matches, struct_end)) {
        indentLevel--;
        cout << getIndent() << "}" << endl;
        insideStruct = false;

        // stash the struct name so we can emit the pools
        string S = currentStructName;
        currentStructName.clear();

        // adjust the magic “9” to however many slots you need
        cout << getIndent()
             << S << " " << S << "_mem[9];" << endl;
        cout << getIndent()
             << "int " << S << "_valid[9];" << endl;
        return;
    }

    
    if (regex_search(trimmed, matches, struct_array_decl)) {
        string typename_ = matches[1];
        string varname = matches[2];
        string size = matches[3];
        cout << getIndent() << typename_ << " " << varname << "[" << size << "];" << endl;
        return;
    }
    
    if (regex_search(trimmed, matches, array_decl)) {
        string type = matches[1];
        string varname = matches[2];
        string size = matches[3];
        cout << getIndent() << type << " " << varname << "[" << size << "];" << endl;
        return;
    }

        // ── 11) Arrays of typedef’d types ────────────────────────────────────
        regex user_array(R"(\s*(\w+)\s+(\w+)\s*\[\s*(\d+)\s*\]\s*;)");
        if (regex_search(trimmed, matches, user_array)) {
            cout << getIndent()
                 << matches[1] << " " << matches[2]
                 << "[" << matches[3] << "];"
                 << endl;
            return;
        }
    

        // ── 8) Multi-dimensional arrays ───────────────────────────────────────
        regex multi_array(R"(\s*(bit|bool|byte|short|int|unsigned)\s+(\w+)((\[\s*\w+\s*\]){2,})\s*;)");
        if (regex_search(trimmed, matches, multi_array)) {
            cout << getIndent()
                 << matches[1] << " " << matches[2] << matches[3] << ";"
                 << endl;
            return;
        }
    
        // ── Channel decls ───────────────────────────────────────────────────
        regex chan_pat(R"(\s*chan\s+(\w+)\s*=\s*\[\s*(\d+)\s*\]\s*of\s*\{\s*(.+?)\s*\}\s*;)");
        if (regex_search(trimmed, matches, chan_pat)) {
            cout << getIndent()
                 << "chan " << matches[1]
                 << " = [" << matches[2] << "] of { " << matches[3] << " };"
                 << endl;
            return;
        }
    
            // ── Basic Promela types ───────────────────────────────────────────
        regex dtype(R"(\s*(bit|bool|byte|short|int|unsigned)\s+(\w+)\s*;)");
        if (regex_search(trimmed, matches, dtype)) {
            cout << getIndent()
                << matches[1] << " " << matches[2] << ";"
                << endl;
            return;
        }

        // ── mtype enum ─────────────────────────────────────────────────────
        regex mtype_pat(R"(\s*mtype\s*=\s*\{\s*(.*?)\s*\}\s*;)");
        if (regex_search(trimmed, matches, mtype_pat)) {
            cout << getIndent()
                << "mtype = { " << matches[1] << " };"
                << endl;
            return;
        }

    

    

    
        
    // Match if statement
    if (regex_search(trimmed, matches, if_pattern)) {
        string condition = matches[1];
        cout << getIndent() << "if" << endl;
        indentLevel++;
        cout << getIndent() << ":: (" << condition << ") ->" << endl;
        indentLevel++;
        insideIfElse = true;
        return;
    }
    if (trimmed == "else {") {
    cout << getIndent() << ":: else ->" << endl;
    indentLevel++;
    insideIfElse = true;
    return;
}


// Match else block
// Match else block




    // Function call: foo();


    

regex call_pattern(R"((\w+)\s*\(\s*\)\s*;)");
if (regex_search(trimmed, matches, call_pattern)) {
    if (insideSwitch && !pendingCases.empty()) {
        cout << getIndent() << ":: (";
        for (size_t i = 0; i < pendingCases.size(); ++i) {
            if (i > 0) cout << " || ";
            cout << switchVar << " == " << pendingCases[i];
        }
        cout << ") ->" << endl;
        indentLevel++;
        pendingCases.clear();
    }

    string called_func = matches[1];
    cout << getIndent() << "run " << called_func << "();" << endl;
    if (insideSwitch) indentLevel--;
    return;
}

    // ── assign from &var or &arr[idx]
    static const regex ref_assign(
      R"(\s*(\w+)\s*=\s*&(\w+)(?:\[(\w+)\])?\s*;)"
    );
    if (regex_search(trimmed, matches, ref_assign)) {
        string lhs   = matches[1];
        string base  = matches[2];
        string idx   = matches[3].str();
        cout << getIndent()
             << lhs << " = "
             << base << "_mem[" << (idx.empty() ? "0" : idx) << "];"
             << endl;
        return;
    }

    // ── assign from struct‐field or pointer‐field
    static const regex struct_assign(
      R"(\s*(\w+)\s*=\s*(\w+)(?:->|\.)+(\w+)\s*;)"
    );
    if (regex_search(trimmed, matches, struct_assign)) {
        cout << getIndent()
             << matches[1]
             << " = "
             << matches[2] << "_" << matches[3]
             << ";" << endl;
        return;
    }

        // ── 9) Basic‐type declarations with initialization ─────────────────────
        regex init_decl(R"(\s*(bit|bool|byte|short|int|unsigned)\s+(\w+)\s*=\s*(.+);)");
        if (regex_search(trimmed, matches, init_decl)) {
            cout << getIndent()
                 << matches[1] << " " << matches[2]
                 << " = " << matches[3] << ";"
                 << endl;
            return;
        }

            // ── 10) mtype variable declarations ───────────────────────────────────
    regex mtype_var(R"(\s*mtype\s+(\w+)\s*=\s*(\w+);)");
    if (regex_search(trimmed, matches, mtype_var)) {
        cout << getIndent()
             << "mtype " << matches[1]
             << " = " << matches[2] << ";"
             << endl;
        return;
    }

    

    // ── Handle “i = 0, j = 0, k = 0;” ────────────────────────────────────
if (trimmed.find(',') != string::npos && trimmed.find('=') != string::npos) {
    // drop the trailing ';'
    string body = trimmed.substr(0, trimmed.size() - 1);
    istringstream iss(body);
    string chunk;
    while (getline(iss, chunk, ',')) {
        chunk = regex_replace(chunk, regex("^\\s+|\\s+$"), "");
        cout << getIndent() << chunk << ";" << endl;
    }
    return;
}

        regex printf_pattern(R"(printf\s*\((.*)\);)");
    if (regex_search(trimmed, matches, printf_pattern)) {
        cout << getIndent() << "printf(" << matches[1] << ");" << endl;
        return;
    }
        // ── Handle return statements ─────────────────────────────────────────
        regex return_pattern(R"(\s*return\b(?:\s*\d+)?\s*;)");
        if (regex_search(trimmed, matches, return_pattern)) {
            cout << getIndent() << "return;" << endl;
            return;
        }
    

    // ── malloc/free & pointers (stubs) ─────────────────────────────────
regex malloc_pat(R"(\s*(\w+)\s*=\s*\(\w*\*\)\s*malloc\((.+)\);)");
if (regex_search(trimmed, matches, malloc_pat)) {
    cout << getIndent()
         << "// " << matches[1]
         << " = malloc(" << matches[2] << ");  (not supported)"
         << endl;
    return;
}
regex free_pat(R"(\s*free\s*\(\s*(\w+)\s*\);)");
if (regex_search(trimmed, matches, free_pat)) {
    cout << getIndent()
         << "// free(" << matches[1] << ");  (no-op)"
         << endl;
    return;
}
regex ptr_decl(R"(\s*(int|byte|short|bool)\s*\*\s*(\w+)\s*;)");
if (regex_search(trimmed, matches, ptr_decl)) {
    cout << getIndent()
         << "// pointer " << matches[1] << "* " << matches[2]
         << " (manual handling)"
         << endl;
    return;
}

    // Match: int gcd(int x, int y) {


static vector<string> returnChannelNames;





regex func_args_pattern(R"((?:int|void|byte|short|bool)\s+(\w+)\s*\(([^)]*)\)\s*\{)");
if (regex_search(trimmed, matches, func_args_pattern)) {
    string func_name = matches[1];
    string args = matches[2];
    currentFunctionName = func_name;
    insideFunction = true;

    vector<string> argsList;
    istringstream argstream(args);
    string arg;
    while (getline(argstream, arg, ',')) {
        arg = regex_replace(arg, regex("^\\s+|\\s+$"), "");
        if (!arg.empty()) argsList.push_back(arg);
    }

    cout << getIndent() << "proctype " << func_name << "(chan ret_" << func_name;
    for (const string& argstr : argsList) {
        smatch argMatch;
        if (regex_search(argstr, argMatch, regex(R"((int|byte|bool|short)\s+(\w+))"))) {
            cout << "; " << argMatch[1] << " " << argMatch[2];
        }
    }
    cout << ") {" << endl;
    indentLevel++;
    return;
}

// ── Phase 1: match “if(cond) return X;” ───────────────────────────────
static const regex if_return_pat(
    R"(^\s*if\s*\(\s*(.+?)\s*\)\s*return\s+([^;{}]+?)\s*;?\s*\}?\s*$)"
);
bool endsWithBrace = trimmed.find("}") != string::npos;



if (regex_search(trimmed, matches, if_return_pat)) {
    sawIfReturn = true;
    string cond = matches[1], expr = matches[2];

    cout << getIndent() << "if\n";
    indentLevel++;
    cout << getIndent() << ":: (" << cond << ") ->\n";
    indentLevel++;
    cout << getIndent()
         << "ret_" << currentFunctionName
         << " ! " << expr << ";\n";
    cout << getIndent() << "goto end;\n";
    if (endsWithBrace) {
    indentLevel--;
    cout << getIndent() << "fi;" << endl;
    indentLevel--;
    cout << getIndent() << "end:" << endl;
    cout << getIndent() << "printf(\"End of " << currentFunctionName << "\\n\");" << endl;
    cout << getIndent() << "}" << endl;
    insideFunction = false;
    currentFunctionName.clear();
}

    indentLevel--;
    return;  // wait for the else
}


    // ── Bare “else” after an if–return ────────────────────────────────────
    if (insideFunction && sawIfReturn && trimmed == "else") {
        cout << getIndent() << ":: else ->" << endl;
        indentLevel++;
        return;
   }

// ── Phase 2: match “else return Func(args);” ───────────────────────────
static const regex else_return_pat(
    R"(^\s*else\s*return\s+(\w+)\s*\((.*)\)\s*;)"
);

    // ── Return‐call inside the else branch ────────────────────────────────
    static const regex return_func_pat(
        R"(^\s*return\s+(\w+)\s*\((.*?)\)\s*;)"
    );
    if (insideFunction && sawIfReturn
       && regex_search(trimmed, matches, return_func_pat)) {
        sawIfReturn = false;
        string callee = matches[1], args = matches[2];

        // emit the body of our “else” branch
        cout << getIndent()
             << "run " << callee
             << "(ret_tmp, " << args << ");" << endl;
        cout << getIndent() << "ret_tmp ? tmp;" << endl;
        cout << getIndent()
             << "ret_" << currentFunctionName
             << " ! tmp;" << endl;
        cout << getIndent() << "goto end;" << endl;

       // close out the if…fi and the proctype
        indentLevel--;                 // outdent from else‐branch
        cout << getIndent() << "fi;" << endl;
        cout << getIndent() << "end:" << endl;
        cout << getIndent()
             << "printf(\"End of " << currentFunctionName << "\\n\");" << endl;
        cout << getIndent() << "}" << endl;
        insideFunction = false;
        currentFunctionName.clear();
        return;
    }

regex call_args_pattern(R"((\w+)\s*\(\s*(.*?)\s*\)\s*;)");
if (regex_search(trimmed, matches, call_args_pattern)) {
    string callee = matches[1];
    string args = matches[2];
    
    // Check if the call is in a return context (like assignment or conditional)
    if (insideFunction && sawIfReturn) {
        // This is handled in the "else return" logic, skip here
        return;
    }

    cout << getIndent()
         << "run " << callee
         << "(ret_tmp, " << args << ");" << endl;
    cout << getIndent() << "ret_tmp ? tmp;" << endl;
    return;
}

// ── Inline return like “return n;” ───────────────────────────────────────────
regex simple_return_expr(R"(\s*return\s+([^\s;]+)\s*;)");
if (regex_search(trimmed, matches, simple_return_expr)) {
    string expr = matches[1];

    // If we just saw an if(cond) return …;, this is the else‐branch:
    if (insideFunction && sawIfReturn) {
        cout << getIndent() << ":: else   -> ";
        sawIfReturn = false;           // consume the pending if-return
        insideIfElse = false;          // close out insideIfElse
    }

    cout << "ret_" << currentFunctionName
         << " ! " << expr << ";" << endl;
    cout << getIndent() << "goto end;" << endl;

    // Now close the if…fi and emit end‐label
    cout << getIndent() << "fi;" << endl;
    return;
}

static const regex return_func_call(R"(return\s+(\w+)\((.*?)\);)");
if (regex_search(trimmed, matches, return_func_call)) {
    string callee = matches[1];
    string args = matches[2];
    string tmpVar = "tmp";
    string retChan = "ret_tmp";

    cout << getIndent() << "chan " << retChan << " = [0] of { int };" << endl;
    cout << getIndent() << "int " << tmpVar << ";" << endl;
    cout << getIndent() << "run " << callee << "(" << retChan << ", " << args << ");" << endl;
    cout << getIndent() << retChan << " ? " << tmpVar << ";" << endl;
    cout << getIndent() << "ret_" << currentFunctionName << " ! " << tmpVar << ";" << endl;
    cout << getIndent() << "goto end;" << endl;
    return;
}
   // allow array-indices and == inside conditions get split separately
regex expr_pattern(R"(([\w\[\]\.]+)\s*=\s*(.+);)");


    if (regex_search(trimmed, matches, expr_pattern)) {
        
        if (insideSwitch && !pendingCases.empty()) {
            cout << getIndent() << ":: (";
            for (size_t i = 0; i < pendingCases.size(); ++i) {
                if (i > 0) cout << " || ";
                cout << switchVar << " == " << pendingCases[i];
            }
            cout << ") ->" << endl;
            indentLevel++;
            pendingCases.clear();
        }

        string lhs = matches[1];
        string rhs = matches[2];
        cout << getIndent() << lhs << " = " << rhs << ";" << endl;
        if (insideSwitch) indentLevel--;
        return;
    }
    regex full_return_direct(R"(\\s*return\\s+(\\w+)\\s*;)"), full_return_call(R"(\\s*return\\s+(\\w+)\\((.*?)\\)\\s*;)");
if (regex_search(trimmed, matches, full_return_direct)) {
    cout << getIndent() << "ret_" << currentFunctionName << " ! " << matches[1] << ";" << endl;
    cout << getIndent() << "goto end;" << endl;
    return;
}
regex init_pattern(R"(init\s*\{)");
if (regex_search(trimmed, matches, init_pattern)) {
    cout << getIndent() << "init {" << endl;
    indentLevel++;
    return;
}

regex main_pattern(R"(int\s+main\s*\(\s*\)\s*\{)");
if (regex_search(trimmed, matches, main_pattern)) {
    currentFunctionName = "main";
    insideFunction = true;
    cout << getIndent() << "proctype main(chan ret_main) {" << endl;
    indentLevel++;
    return;
}
    



// ── Closing brace: }
if (trimmed == "}") {
    // 1) Finish an if…else first
    if (insideIfElse) {
        indentLevel--;
        //cout << getIndent() << "fi;" << endl;
        //insideIfElse = false;
        return;
    }

    // 2) Close a do…od loop if we’re in one
 if (!loopStack.empty()) {
//-    string cond = loopStack.back();
   string iterExpr = loopStack.back();
     loopStack.pop_back();

     indentLevel--;  // outdent from the loop body
    // if this was a for-loop, emit its iterator
    if (!iterExpr.empty()) {
        cout << getIndent() << iterExpr << ";" << endl;
             cout << getIndent() << ":: else -> break;" << endl;

    }
     // always close with the break-guard
     indentLevel--;  // outdent from the 'do'
     cout << getIndent() << "od" << endl;
     return;
 }




    // 3) Close a switch…fi if we’re in one
    if (insideSwitch) {
        indentLevel--;             // outdent from switch-if
        cout << getIndent() << "fi" << endl;
        insideSwitch = false;
        pendingCases.clear();
        return;
    }
    if (insideFunction) {
        cout << getIndent() << "end:" << endl;
        cout << getIndent() << "printf(\"End of " << currentFunctionName << "\\n\");" << endl;
        indentLevel--;
        cout << getIndent() << "}" << endl;

        // ← YOU ARE HERE: insideFunction==true just closed *some* proctype
        bool wasMain = (currentFunctionName == "main");
        insideFunction = false;
        currentFunctionName.clear();

        if (wasMain) {
            // only after main, emit init
            cout << "init {" << "\n"
                 << "    chan ret_main = [0] of { int };" << "\n"
                 << "    run main(ret_main);"  << "\n"
                 << "    ret_main ? tmp;"      << "\n"
                 << "}"                      << endl;
        }

        return;
    }

    // 4) Normal block close
    indentLevel--;
    cout << getIndent() << "}" << endl;
    return;
}


    cerr << "Unrecognized or unsupported: " << line << endl;
}

int main() {
    // Open the input C source
    ifstream infile("input.c");
    if (!infile.is_open()) {
        cerr << "Error: Could not open input.c" << endl;
        return 1;
    }

    // Create the Promela output file
    ofstream outfile("output.spin");
    if (!outfile.is_open()) {
        cerr << "Error: Could not create output.spin" << endl;
        return 1;
    }

    // ── Redirect all cout into output.spin ─────────────────────────────────────
    auto old_buf = cout.rdbuf(outfile.rdbuf());

    string line;
    while (getline(infile, line)) {
        if (line.empty()) continue;
        parseExpression(line);
    }

    // ── Restore cout back to the console ───────────────────────────────────────
    cout.rdbuf(old_buf);

    infile.close();
    outfile.close();

    // Optional: print completion message to console
    cout << "✅ Translation complete. Output saved to: output.spin" << endl;

    return 0;
}