   regex struct_start(R"(\s*struct\s+(\w+)\s*\{)");
    regex struct_field(R"(\s*(int|byte|short|bool)\s+(\w+)\s*;)");
    regex struct_end(R"(\s*\};)");
    regex struct_array_decl(R"(\s*struct\s+(\w+)\s+(\w+)\[(\d+)\];)");
    regex array_decl(R"((int|byte|short|bool)\s+(\w+)\[(\d+)\];)");