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
