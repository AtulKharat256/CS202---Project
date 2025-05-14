proctype main(chan in_main) {
    int x = 0, a = 1, b = 2;
    if
        :: (x == 0) ->
            a++;
        b++;
    break;
    :: (x == 1) ->
        a--;
    b--;
break;
:: else ->
    break;
fi
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
