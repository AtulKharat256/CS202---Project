typedef node {
    node* next;
    int value;
}
node node_mem[9];
int node_valid[9];
proctype test(chan in_test) {
    atomic {
        int malloc_node_c = 1;
        do
            :: (malloc_node_c >= 9) -> break
            :: else ->
                if
                    :: (node_valid[malloc_node_c] == 0) ->
                        node_valid[malloc_node_c] = 1;
                        break
                :: else -> malloc_node_c++
            fi
    od;
    assert(malloc_node_c < 9);
    tmp = malloc_node_c
    new = tmp;
};
d_step {
    node_valid[new] = 0;
    node_mem[new].next = 0;
    node_mem[new].value = 0;
};
in_test ! 0;
goto end;
end:
printf("End of test\n");
}
