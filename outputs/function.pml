proctype test(chan in_test; int a; int b) {
    if
        :: (a >= b) ->
            ret_test ! a;
            goto end;
        :: else   -> ret_test ! b;
        goto end;
        fi;
        in_test ! 0;
        goto end;
        end:
        printf("End of test\n");
    }
    proctype main(chan in_main) {
        int x = 2;
        int y = 3;
        int result = test(x, y);
        in_main ! 0;
        goto end;
        end:
        printf("End of main\n");
    }
init {
    chan ret_main = [0] of { int };
    run main(ret_main);
    ret_main ? tmp;
}
