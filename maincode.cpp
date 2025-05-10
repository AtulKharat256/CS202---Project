#include <iostream>
#include <fstream>
#include <regex>
#include <string>

using namespace std;

int indentLevel = 0;

string getIndent() {
    if (indentLevel < 0) indentLevel = 0;
    return string(indentLevel * 4, ' ');
}


void parseExpression(const string& line) {
    smatch matches;
    static bool insideSwitch = false;
    static string switchVar;
    static vector<string> pendingCases;

    string trimmed = regex_replace(line, regex("^\\s+|\\s+$"), "");
    static bool insideIfElse = false;

    regex if_pattern(R"(\s*if\s*\(([^)]+)\)\s*\{)");
    regex else_pattern(R"(\s*else\s*\{)");

    // Struct handling state
    static bool insideStruct = false;
    static string currentStructName;
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


    regex inc_pattern(R"((\w+)\s*\+\+\s*;)");
    regex dec_pattern(R"((\w+)\s*\-\-\s*;)");
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

    // Struct and array support
    regex struct_start(R"(\s*struct\s+(\w+)\s*\{)");
    regex struct_field(R"(\s*(int|byte|short|bool)\s+(\w+)\s*;)");
    regex struct_end(R"(\s*\};)");
    regex struct_array_decl(R"(\s*struct\s+(\w+)\s+(\w+)\[(\d+)\];)");
    regex array_decl(R"((int|byte|short|bool)\s+(\w+)\[(\d+)\];)");

    // Function definition: void foo() {
    regex func_pattern(R"((?:void|int|byte|bool|short)\s+(\w+)\s*\(\s*\)\s*\{)");
    if (regex_search(trimmed, matches, func_pattern)) {
        string func_name = matches[1];
        cout << getIndent() << "proctype " << func_name << "() {" << endl;
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
    
    if (insideStruct && regex_search(trimmed, matches, struct_end)) {
        indentLevel--;
        cout << getIndent() << "}" << endl;
        insideStruct = false;
        currentStructName.clear();
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
    

    // Main function: int main() {
    regex main_pattern(R"(int\s+main\s*\(\s*\)\s*\{)");
    if (regex_search(trimmed, matches, main_pattern)) {
        cout << getIndent() << "init {" << endl;
        indentLevel++;
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

// Match else block
// Match else block
    if (regex_search(trimmed, matches, else_pattern)) {
        indentLevel--; // End previous if branch
        cout << getIndent() << ":: else ->" << endl;
        indentLevel++;
        return;
    }



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


    // Assignment expression: a = b + c;
    regex expr_pattern(R"((\w+)\s*=\s*(.+);)");
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

    // Closing brace: }
    if (trimmed == "}") {
        if (insideSwitch) {
        if (indentLevel > 0) indentLevel--;
        cout << getIndent() << "fi" << endl;
        insideSwitch = false;
        pendingCases.clear();
        return;
    }

        if (insideIfElse) {
            // We're closing a branch (if or else), not a normal block
            indentLevel--;  // close :: branch
            // If this is the final closing brace of the full if-else
            static int ifBranchCount = 0;
            ifBranchCount++;
            if (ifBranchCount == 2) {
                if (indentLevel > 0) indentLevel--;
                cout << getIndent() << "fi" << endl;
                insideIfElse = false;
                ifBranchCount = 0;
            
                if (indentLevel > 0) indentLevel--;
                cout << getIndent() << "}" << endl;
            }
            
            return;
        } else {
            // Normal function or init block
            indentLevel--;
            cout << getIndent() << "}" << endl;
            return;
        }
    }
    
    
    

    cerr << "Unrecognized or unsupported: " << line << endl;
}

int main() {
    ifstream infile("input.c");
    if (!infile.is_open()) {
        cerr << "Error: Could not open input.c" << endl;
        return 1;
    }

    ofstream outfile("output.spin");
    if (!outfile.is_open()) {
        cerr << "Error: Could not create output.spin" << endl;
        return 1;
    }

    string line;
    while (getline(infile, line)) {
        if (line.empty()) continue;

        // Redirect cout to output.spin
        streambuf* old_buf = cout.rdbuf();
        cout.rdbuf(outfile.rdbuf());

        parseExpression(line);

        // Restore cout to console
        cout.rdbuf(old_buf);
    }

    infile.close();
    outfile.close();

    cout << "✅ Translation complete. Output saved to: output.spin" << endl;
    ifstream result("output.spin");
    if (!result.is_open()) {
        cerr << "Error: Could not read back output.spin" << endl;
        return 1;
    }

    cout << "\n🔍 Final Output in output.spin:\n\n";
    string lineOut;
    while (getline(result, lineOut)) {
        cout << lineOut << endl;
    }
    result.close();

    return 0;
}