if
    :: (flag == 0) ->
        tries++;
    :: (flag == 1) ->
        retries--;
:: else ->
    done = 1;
fi
