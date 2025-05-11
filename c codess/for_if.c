int i;
for (i = 0; i < 5; i++) {
    if (i == 2) continue;
    if (i == 4) break;
    process(i);
}
