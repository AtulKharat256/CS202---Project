proctype test(chan ret_test) {
    run malloc(ret_tmp, sizeof(struct node));
    ret_tmp ? tmp;
    // free(p);  (no-op)
    end:
    printf("End of test\n");
}
