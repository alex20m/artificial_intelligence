variables i0,i1, i2, i3, o0, o1, o2, o3, c, a1, a2, a3;

o0 <-> (not i0);
o1 <-> (i0 xor i1);
o2 <-> (a1 xor i2);
o3 <-> (a2 xor i3);

a1 <-> (i0 and i1);
a2 <-> (a1 and i2);
a3 <-> (a2 and i3);

c <-> a3;