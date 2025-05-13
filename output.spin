typedef node {
    node* next;
    int value;
}
node node_mem[9];
int node_valid[9];
node* tail;
proctype test(chan ret_test) {
    next = temp;
    tail = temp;
    end:
    printf("End of test\n");
}
