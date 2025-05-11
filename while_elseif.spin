int i = 0;
do
    :: (i < 4) ->
        if
            :: (i % 2 == 0) ->
                printf("even\n");
            :: else ->
                printf("odd\n");
            fi;
            i++;
        :: else -> break;
    od;
