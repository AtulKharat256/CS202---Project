proctype gcd(chan ret_gcd; int x; int y) {
    if
        :: (y == 0) ->
            ret_gcd ! x;
            goto end;
        :: else ->
            run gcd(ret_tmp, y, x % y);
            ret_tmp ? tmp;
            ret_gcd ! tmp;
            goto end;
        fi;
        end:
        printf("End of gcd\n");
    }
