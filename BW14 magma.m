x:=2565121;
//x:=1+2^10+2^13-2^16+2^19+2^21;
seed:=x;
r:=x^12-x^10+x^8-x^6+x^4-x^2+1;
t:=1+x^2;
p:=(x^18-2*x^16+x^14+x^4+2*x^2+1) div 4;
Fp:=GF(p);
F7<u>:=ExtensionField<Fp,u|u^7-17>;
F14<v>:=ExtensionField<F7,v|v^2-u>;
E:=EllipticCurve([F14|1,0]);
E1:=EllipticCurve([Fp|1,0]);
Et:=EllipticCurve([F7|u^2,0]);
Ett:=EllipticCurve([F14|u^2,0]);    //twist curves
//for the non-trivial automorphism
beta:=4506128361793112414031596301001191791829240001521837523639000497831654632776289077711270335522484434220968961;
//final exponentiation
f := 5715386406791036496338449727773518121913537339153558598769019100899610655894088\
0448510936973404566850144047253855083588084908422723394763776019097175206156568\
0001818096385265238478648846440740575460421402964492686722752494375115141693538\
1462558542907467640798495389126290040250657097473905787290584806459344873548283\
5695629597910053135958166370581870394224076358319578848247741935294841863701123\
0946572020209292924505359067575272559862917800323780741672595434760897581838027\
3021892759535696773104240287010424804758911973455371747906620434862585736264549\
7041655821648826349202166801183827741238866609272861617630373656248542268992003\
9059494999964945548308356040697950884446633849853154114263288288690319722416016\
4025071055056192588316066852931978639016745579303339117052109769923468166147643\
0499910362858474821011365083024295066366594459368793416225844815666271531947967\
2041689804103987816527700123173849338313605451625374326836243595125826463164840\
4876814965083065012341400097658174920543957659628599967660255352965887399084872\
9355752087983139219553114983098376945622491082530668395894606634755968422273359\
1482866484996920820696772654507437785339810210856662872513539110544795392442798\
1853549101916520286555320809493949190930423212409352044817828767485207928761707\
8539345784717190692088495205233630503332400833877521188461424419093921819570957\
6737347635374360932795532439881913550077078875470433251319460764539466598260271\
4061631157063087251637102999961664527009957586977613874255101693552007679903780\
63275422310970422911323074560;

px:=0x1492C89B8D21EAE5F8636F8A233EF85FD6671321D875BCDB077AC855D539AF565551C018CE18C0510CA30A26A0C7F553;
py:=0x1DD9ACF65BEE2A98F07EDA8A0E6929324E1D265A26D6B8C623D0990517248658E79B4560248D6E2F117919A26EC215DE;

qx:=[];
qx[1]:=0x21AFDDA809D73F1FAA6E41D252343755A5A951A9AF982FC2E1EB5C8C23238931F3FD08750C31580D80CF530B2088496B;
qx[2]:=0x1E2C900556F4943C8FC6D8EAE97244151D997B091CB886B8B5669EF951BD039F1E3977ABBF79B459989ACBD034582D21;
qx[3]:=0x2556C8E973AA254204E445605239C26BE78C9B7089DCFB2A2A22D0E04D3AD15C6B4F8C1574C080E0F279A7D416169B0D;
qx[4]:=0x112C6FF918F94BE128488FC019E6B242AFAEC177F2BF9CBFCDA51410DE6CEC9558DC0B6F4EFF378404727E271C7244FF;
qx[5]:=0x2345D63B89C4FF3D9126F885FBABE0FA2001BFC2BE4613930F61A56B8EC57DA59F3EFDD3F80C5A1B964E9C4037A56113;
qx[6]:=0x1E2ABBAAA7AD9BE5C3112361344E1DBE68B91A725226FA512ACD2C431580B0435DDF80B67777E8EF0F10F74257EE138E;
qx[7]:=0x109D7184DBFF80F6DCB6D9347E82A7974648135D9B21C7665A7D3F629C8D7D47AFBAF922F2CF90D7966A7DC077EA9193;
qy:=[];
qy[1]:=0x166685A1D20CA613FC9A3EB1E9C8193B082D587A612DD134E6DD1BBB8E1A36923556ADB3049695D0B050000038D4A493;
qy[2]:=0x1672AC76E3B1A7AD308AA3611DC0EA61F856F326CE61801AF646E1C25B859C0E9E4DD5DCCBA9BB39214D1C2FE7F6C0DC;
qy[3]:=0x142F7A22645CC0D88FEC2543A5FDA2D6848929C040C58F5AA0D1158624CFB4B2101A7FF21377B5B0D2192AB551442153;
qy[4]:=0xD5CB93F39080178D15B770F029B22B83C5DA8941C411119A395B72E5A34B8E7A02AFBA5026F55C51E04413CA2A55032;
qy[5]:=0xCAE1D358A2AF184B93BD00D1B06FE6728828AA1A3C76EC0B8D3B6E8B8245DED41E7519D569D8D084C078A2E4C2B22E2;
qy[6]:=0x14B7853245656BD427DA137FA2A19D09664BB7249BA9CC73DC140E2A872EBB5842E2399A7E44F56AAD6BF0AF763BEFB2;
qy[7]:=0x16D7D028F257445448ACB50EF489AA4457DCB5EACA1EA4A3C6F999576CF0244A4651D834804A3B7F1345579DB9ADDE26;

Qx := [qx[i] * u^(i - 1) : i in [1..7]];
Qy := [qy[i] * u^(i - 1) : i in [1..7]];
Qx:=&+Qx;
Qy:=&+Qy;
qx:=Qx;
qy:=Qy;
PP:=E1![px,py];
QQ:=Et![qx,qy];

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

//final exponentiation and the cubical ladder computation simultanously
//store the value of nQ inside the array s
function ladder3exposimul(n, a, Q, PQ, xP, phi1PQ, xphi1P, ixQ, ixQmP, ixQmphi1P)
    nbits := Reverse(Intseq(n, 2)); 
    s:=[[F7!0,F7!0,F7!0,F7!0] : i in [1 .. #nbits]];

    s[1][3], s[1][4] := double(a, Q);

    s[1][3], s[1][4] := diff_add(a, [s[1][3], s[1][4]], [Q[1], Q[2]], 1, ixQ);
    XPnQ, ZPnQ := diff_add(a, [(PQ)[1], (PQ)[2]], [Q[1], Q[2]], xP, 1);
    s[1][1], s[1][2] := double(a, [Q[1], Q[2]]);
    for bit := 2+1 to #nbits do
        if nbits[bit] eq 0 then
            s[bit-1][3], s[bit-1][4] := diff_add(a, [s[bit-1-1][3], s[bit-1-1][4]], [s[bit-1-1][1], s[bit-1-1][2]], 1, ixQ);
            XPnQ, ZPnQ := diff_add(a, [XPnQ, ZPnQ], [s[bit-1-1][1], s[bit-1-1][2]], xP, 1);
            s[bit-1][1], s[bit-1][2] := double(a, [s[bit-1-1][1], s[bit-1-1][2]]);
        else
            s[bit-1][1], s[bit-1][2] := diff_add(a, [s[bit-1-1][3], s[bit-1-1][4]], [s[bit-1-1][1], s[bit-1-1][2]], 1, ixQ);
            XPnQ, ZPnQ := diff_add(a, [s[bit-1-1][3], s[bit-1-1][4]], [XPnQ, ZPnQ], 1, ixQmP);
            s[bit-1][3], s[bit-1][4] := double(a, [s[bit-1-1][3], s[bit-1-1][4]]);
        end if;
    end for;

    Xphi1PnQ, Zphi1PnQ := diff_add(a, [(phi1PQ)[1]*ZPnQ^(p^10), (phi1PQ)[2]*ZPnQ^(p^10)], [Q[1], Q[2]], xphi1P, 1);
    for bit := 2+1 to #nbits do
        if nbits[bit] eq 0 then
            Xphi1PnQ, Zphi1PnQ := diff_add(a, [Xphi1PnQ, Zphi1PnQ], [s[bit-1-1][1], s[bit-1-1][2]], xphi1P, 1);
        else
            Xphi1PnQ, Zphi1PnQ := diff_add(a, [s[bit-1-1][3], s[bit-1-1][4]], [Xphi1PnQ, Zphi1PnQ], 1, ixQmphi1P);
            Xphi1PnQ := Xphi1PnQ * ZPnQ^(p^10);
            Zphi1PnQ := Zphi1PnQ * ZPnQ^(p^10);
        end if;
    end for;
    return Zphi1PnQ;
end function;

function sopbw14exposimul(Q,P)
    px:=P[1];
    py:=P[2];
    qx:=Q[1];
    qy:=Q[2];   //px py in Fp,  qx qy in Fp7
    n:=seed;
    a:=u^2;
    xQmP:=17*px+px*qx^2*u^5+qx*(px^2+1)*u^6 + 2*py*qy*u^5*v;
    xQmP:=xQmP*u;
    zQmP:=17*px^2 -2*u^6*px*qx +u^5*qx^2;
    PQ1:=(17*px+px*qx^2*u^5+qx*(px^2+1)*u^6 - 2*py*qy*u^5*v)*u;
    PQ2:=17*px^2 -2*u^6*px*qx +u^5*qx^2;
    PQ:=[PQ1, PQ2];

    xP:=px*u;
    xQ:=Q[1];
    zQ:=1;

    phi1P:=E1![px*(-1),-1*beta*py];
    xQmphi1P:=-17*px-px*qx^2*u^5+qx*(px^2+1)*u^6 - beta*2*py*qy*u^5*v;
    xQmphi1P:=xQmphi1P*u;           //X(Q-\phi^{-1}(P))
    zQmphi1P:=17*px^2 +2*u^6*px*qx +u^5*qx^2;         //Z(Q-\phi^{-1}(P))
    phi1PQ1:=(-17*px-px*qx^2*u^5+qx*(px^2+1)*u^6 + beta*2*py*qy*u^5*v);
    phi1PQ1:=phi1PQ1*u;
    phi1PQ2:=zQmphi1P;
    phi1PQ:=[phi1PQ1,phi1PQ2];      //[X(Q+\phi^{-1}(P)), Z(Q+\phi^{-1}(P))]
    xphi1P:=-1*xP;

    xQ:=Q[1];
    zQ:=1;
    ixQ:=zQ/xQ;
    ixQmP:=zQmP/xQmP;
    ixQmphi1P:=zQmphi1P/xQmphi1P;
    result:=ladder3exposimul(n, a, [xQ,1], PQ, xP, phi1PQ, xphi1P, ixQ, ixQmP, ixQmphi1P);
    return result^f;
end function;

if sopbw14exposimul(QQ*23,PP) eq sopbw14exposimul(QQ,PP)^23 and sopbw14exposimul(QQ,PP*23) eq sopbw14exposimul(QQ,PP)^23 then
    printf "bilinear\n";
else
    printf "non-bilinear\n";
end if;
if sopbw14exposimul(QQ, PP) eq 1 then
    printf "degenerate\n";
else
    printf "non-degenerate\n";
end if;