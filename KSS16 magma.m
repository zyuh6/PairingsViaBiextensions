p := 1256028785022992686281976800775584186790077152694705296490733913907463653887495118497881818417348781; 
r := 76749303233644362810031761312494251479976520114737095173470124054706229421873;
t := 63397887280072706864304625873363576159480517236282;
//lamb := t - 1;
seed:= 16181641185;
Fp :=GF(p);
Fp4<u>:=ExtensionField<Fp,u|u^4 + 2>;
Fp8<v>:=ExtensionField<Fp4,v|v^2 - u>;
Fp16<w>:=ExtensionField<Fp8,w|w^2 - v>;
E:= EllipticCurve([Fp|1,0]);
E16:= EllipticCurve([Fp16|1,0]);
Etwist := EllipticCurve([Fp4|u,0]);
Etwist16 := EllipticCurve([Fp16|u,0]);

P:=Etwist16![0x033596D1D0B1FEB292325D72BB9872B1A8DF543FFFFF83B0802DC45CA4B714C533D085235CD2F470111*v,0x1FCDBF207B0F767A67CFCFB017C7EEB580CF5C9D39B6D872AE2F091E12028107C097DCB606B30388E5D*v*w];
X0:=0x0A8E1814295DCD3B32115B7ECA482E00E799D573C1C87226DF403C088C4E0D6867D0F782463D75EF703;
X1:=0x1C35DF89EBA1F4F7F0914CCC2217236A2DEBD627A4140DB7DE5B6C34B64CBFEB0D6A81D37175FC2D2D0;
X2:=0x121D8B058C749480DBD0C3B80A7A87A6062EAFBA48C38A4209D366182B5CF34144A63EA4D2D22A49810;
X3:=0x13DD1C6C7EF26A3BE18758FDD4DA5B1FC973B9C7B2FE6F95742E63209743DA5DC9D78508FFF7D6577F5;
Y0:=0x1D6E4D1204B71D526B26E4F9659A56950863CA7A11798AD0002A662C94925555508BDC74A72AFF20761;
Y1:=0x174D707AAB7BE8D7FD66A81C116C35FAA3DE173AF8E78EBF4D21946D1DAE273D2F01D18BF58FB6774F9;
Y2:=0x07B52F66D7F4F13D402C90F25289B984F4803D5AB4C5D27C38205B96A35D4BA7E21128C628CB8533252;
Y3:=0x230B103DC9594C0EAC2F136CAF4CC297EE32FBB5D6F2EB1F39F73ED0715410E528827C27A28E47E32C3;

Q:=Etwist16![X0+X1*u^2+X2*u+X3*u^3, Y0+Y1*u^2+Y2*u+Y3*u^3];

function diff_add(a, P, Q, xPmQ, zPmQ)
    XP := P[1];
    ZP := P[2];
    XQ := Q[1]; 
    ZQ := Q[2];
    XPZQ := XP*ZQ;
    XQZP := XQ*ZP;
    b := (XP + ZP)*(XQ - a*ZQ) - XQZP + a*XPZQ;
    c := b^2;
    d := (XPZQ - XQZP)^2;
    XPQ := c * zPmQ;
    ZPQ := d * xPmQ;
    return XPQ, ZPQ;
end function;

function double(a, P)
   X := P[1];
   Z := P[2];
   XP2 := X^2;
   ZP2 := Z^2;
   b := a * ZP2;
   X2 := (XP2 - b)^2;
   c := 4*X*Z;
   Z2 := c*(XP2 + b);
   return X2, Z2;
end function;
//cubical ladder    //simply modify to reduce one diff_add  //start from Q-P instead of Q+P
function ladder3new(n, a, Q, PQ, xP, xQ, zQ, xQmP, zQmP)
    XnQ := Q[1];
    ZnQ := Q[2];
    XPnQ := (PQ)[1];
    ZPnQ :=  (PQ)[2]; 
    XnQQ, ZnQQ := double(a, Q);
    if n eq 2 then
        XPnQ, ZPnQ := diff_add(a, [XPnQ, ZPnQ], [XnQ , ZnQ], xP, 1);
        return XnQQ, ZnQQ, XPnQ, ZPnQ;
    end if;
    nbits := Reverse(Intseq(n, 2));
    for bit := 2 to #nbits do
        XR, ZR := diff_add(a, [XnQQ, ZnQQ], [XnQ, ZnQ], 1, zQ/xQ);
        if nbits[bit] eq 0 then
            XPnQ, ZPnQ := diff_add(a, [XPnQ, ZPnQ], [XnQ, ZnQ], xP, 1);
            XnQ, ZnQ := double(a, [XnQ, ZnQ]);
            XnQQ := XR;
            ZnQQ := ZR;
        else
            XPnQ, ZPnQ := diff_add(a, [XnQQ, ZnQQ], [XPnQ, ZPnQ], 1, zQmP/xQmP);
            XnQQ, ZnQQ := double(a, [XnQQ, ZnQQ]);
            XnQ := XR;
            ZnQ := ZR;
        end if;
    end for;
    return XnQ, ZnQ, XPnQ, ZPnQ;
end function;
//three way add
function add(a, P1, P2, Q, P1Q, P2Q)
    XP1:= P1[1];
    ZP1 := P1[2];
    XP2 := P2[1];
    ZP2 := P2[2];
    XQ := Q[1];
    ZQ := Q[2];
    XP1Q := P1Q[1];
    ZP1Q := P1Q[2];
    XP2Q := P2Q[1];
    ZP2Q := P2Q[2];

    k00 := (XP1*XP2-a*ZP1*ZP2)^2;
    k11 := (XP1*ZP2-XP2*ZP1)^2; 
    k01 := 2*(XP1*XP2 + a*ZP1*ZP2)*(XP1*ZP2 + XP2*ZP1);

    k00b := (XP1Q*XP2Q-a*ZP1Q*ZP2Q)^2;
    k11b := (XP1Q*ZP2Q-XP2Q*ZP1Q)^2;
    k01b := 2*(XP1Q*XP2Q + a*ZP1Q*ZP2Q)*(XP1Q*ZP2Q + XP2Q*ZP1Q);

    XP1mP2 := k01b*k00-k01*k00b;
    ZP1mP2 := k11b*k00-k11*k00b;

    nZP1P2Q := (XP2*ZP1Q-XP1Q*ZP2)*(XP1*ZP2Q-XP2Q*ZP1);
    dZP1P2Q := (XP1mP2*ZQ-ZP1mP2*XQ);

    nXP1P2Q := (XP2*XP1Q-a*ZP1Q*ZP2)*(XP1*XP2Q-a*ZP2Q*ZP1);
    dXP1P2Q := (XP1mP2*XQ-a*ZP1mP2*ZQ);

    XP1P2 := k00*ZP1mP2 * dXP1P2Q*dZP1P2Q;
    ZP1P2 := k11*XP1mP2 * dXP1P2Q*dZP1P2Q;
    XP1P2Q := nXP1P2Q*dZP1P2Q * XP1mP2*ZP1mP2;
    ZP1P2Q := nZP1P2Q*dXP1P2Q * XP1mP2*ZP1mP2;

    return XP1P2, ZP1P2, XP1P2Q, ZP1P2Q;
end function;
//pairing KSS16
function pkss16(Q, P)
    px:=P[1]/v;     //on E
    py:=P[2]/v/w;   //on E
    qx:=Q[1];       //on E'
    qy:=Q[2];       //on E'
    rx:=(px^2*qx+qx)*(p-1)/2*u^3*v + py*qy*u^3*w + px*qx^2*(p-1)/2*u^3 + px;
    rxv:=px*v + px^2*qx+qx +(p-1)/2*u^3*v*px*qx^2 + u^3*v*w*py*qy;      //on E'
    rz:=px^2 + u^3*v*px*qx + (p-1)/2*u^3*qx^2;
    resultx:=((px - qx/v)^3 - 2*px*(px - qx/v)^2 + (py - qy/v/w)^2);
    resultz:=(qx/v-px)^2;
    rxsv:=px*v + px^2*qx+qx +(p-1)/2*u^3*v*px*qx^2 - u^3*v*w*py*qy;

    n:=seed;
    XnQ,ZnQ,XPnQ,ZPnQ:=ladder3new(n, u, [qx,1], [rxv,rz], px*v, qx, 1, rxsv, rz);

    Xpi3nQ:=(XnQ/v)^(p^3);
    Zpi3nQ:=ZnQ^(p^3);
    Xpi4Q:=(qx/v)^(p^4);
    Zpi4Q:=1;
    Xpi3PnQ:=(XPnQ/v)^(p^3);
    Zpi3PnQ:=ZPnQ^(p^3);
    Xpi4PQ:=(rx)^(p^4);
    Zpi4PQ:=rz^(p^4);

    PP:=E16![P[1]/v, P[2]/v/w];
    QQ:=E16![Q[1]/v, Q[2]/v/w];
    n:=seed;
    pi3nQ:=E16![(n*QQ)[1]^(p^3), (n*QQ)[2]^(p^3)];
    pi4Q:=E16![(QQ)[1]^(p^4), (QQ)[2]^(p^4)];
    pi3PnQ:=E16![(PP+n*QQ)[1]^(p^3), (PP+n*QQ)[2]^(p^3)];
    pi4PQ:=E16![(PP+QQ)[1]^(p^4), (PP+QQ)[2]^(p^4)];

    n:=2;
    X2Q,Z2Q,XP2Q,ZP2Q:=ladder3new(n, u, [qx,1], [rxv,rz], px*v, qx, 1, rxsv, rz);

    r1,r2,r3,r4:=add(1, [Xpi4Q, Zpi4Q], [Xpi3nQ, Zpi3nQ], [PP[1],1], [Xpi4PQ, Zpi4PQ], [Xpi3PnQ, Zpi3PnQ]);
    r1,r2,r3,r4:=add(1, [X2Q/v, Z2Q], [r1, r2], [PP[1],1], [XP2Q/v, ZP2Q], [r3, r4]);
    result:=r3/r1/PP[1];
    result:=result^(IntegerRing()!((p^16-1)/r*(seed/5)^3*14));
    return result;
end function;

if pkss16(Q*23,P) eq pkss16(Q,P)^23 and pkss16(Q,P*23) eq pkss16(Q,P)^23 then
    printf "bilinear\n";
else
    printf "non-bilinear\n";
end if;
if pkss16(Q, P) eq 1 then
    printf "degenerate\n";
else
    printf "non-degenerate\n";
end if;