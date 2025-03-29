#include <math.h>
#include <string.h>
double sigmoid(double x) {
    if (x < 0.0) {
        double z = exp(x);
        return z / (1.0 + z);
    }
    return 1.0 / (1.0 + exp(-x));
}
void score(double * input, double * output) {
    double var0;
    if (input[9] < 6.0) {
        if (input[3] < 0.026008183) {
            var0 = 0.3111739;
        } else {
            if (input[1] < 13.0) {
                if (input[3] < 0.102564104) {
                    var0 = 0.034885574;
                } else {
                    var0 = 0.25735256;
                }
            } else {
                if (input[0] < 13.0) {
                    var0 = -0.21607831;
                } else {
                    var0 = 0.12614253;
                }
            }
        }
    } else {
        if (input[9] < 7.0) {
            if (input[2] < 3.329897) {
                if (input[3] < 0.02259887) {
                    var0 = 0.27453429;
                } else {
                    var0 = -0.08402018;
                }
            } else {
                if (input[8] < 33.0) {
                    var0 = -0.28283262;
                } else {
                    var0 = 0.26164177;
                }
            }
        } else {
            if (input[4] < 0.003562341) {
                if (input[3] < 0.00058559206) {
                    var0 = 0.07849254;
                } else {
                    var0 = -0.27810314;
                }
            } else {
                if (input[8] < 26.0) {
                    var0 = 0.095312364;
                } else {
                    var0 = -0.14913581;
                }
            }
        }
    }
    double var1;
    if (input[0] < 12.0) {
        if (input[3] < 0.11818182) {
            if (input[4] < 0.0003362915) {
                var1 = 0.27112922;
            } else {
                if (input[3] < 0.102564104) {
                    var1 = -0.22120157;
                } else {
                    var1 = 0.19172136;
                }
            }
        } else {
            if (input[3] < 0.16666667) {
                if (input[4] < 0.0003362915) {
                    var1 = 0.044087626;
                } else {
                    var1 = 0.2361894;
                }
            } else {
                var1 = 0.22066763;
            }
        }
    } else {
        if (input[4] < 0.0034864573) {
            if (input[2] < 3.6249003) {
                if (input[4] < 0.0003362915) {
                    var1 = -0.1587717;
                } else {
                    var1 = 0.09744353;
                }
            } else {
                if (input[2] < 3.8588235) {
                    var1 = -0.25302568;
                } else {
                    var1 = 0.0049526272;
                }
            }
        } else {
            if (input[8] < 26.0) {
                if (input[4] < 0.0045634923) {
                    var1 = 0.13221306;
                } else {
                    var1 = 0.2548583;
                }
            } else {
                if (input[2] < 3.7565315) {
                    var1 = -0.22359599;
                } else {
                    var1 = 0.27660644;
                }
            }
        }
    }
    double var2;
    if (input[9] < 6.0) {
        if (input[1] < 13.0) {
            if (input[5] < 0.00001) {
                var2 = 0.24366395;
            } else {
                if (input[2] < 2.08) {
                    var2 = 0.16734251;
                } else {
                    var2 = 0.24286647;
                }
            }
        } else {
            if (input[1] < 19.0) {
                if (input[4] < 0.0003362915) {
                    var2 = -0.08942282;
                } else {
                    var2 = 0.26128298;
                }
            } else {
                if (input[2] < 2.0) {
                    var2 = -0.11723347;
                } else {
                    var2 = 0.21136285;
                }
            }
        }
    } else {
        if (input[9] < 7.0) {
            if (input[2] < 3.329897) {
                if (input[0] < 60.0) {
                    var2 = -0.054129783;
                } else {
                    var2 = 0.21193822;
                }
            } else {
                if (input[8] < 33.0) {
                    var2 = -0.22139457;
                } else {
                    var2 = 0.23105589;
                }
            }
        } else {
            if (input[4] < 0.003562341) {
                if (input[8] < 209.0) {
                    var2 = -0.22014883;
                } else {
                    var2 = 0.21946359;
                }
            } else {
                if (input[0] < 1507.0) {
                    var2 = -0.07137232;
                } else {
                    var2 = 0.26404348;
                }
            }
        }
    }
    double var3;
    if (input[9] < 6.0) {
        if (input[3] < 0.026948052) {
            var3 = 0.22526087;
        } else {
            if (input[3] < 0.10909091) {
                if (input[0] < 13.0) {
                    var3 = -0.17948388;
                } else {
                    var3 = 0.096815586;
                }
            } else {
                if (input[8] < 3.0) {
                    var3 = 0.15336186;
                } else {
                    var3 = 0.2293405;
                }
            }
        }
    } else {
        if (input[9] < 7.0) {
            if (input[2] < 3.329897) {
                if (input[3] < 0.024198428) {
                    var3 = 0.18830547;
                } else {
                    var3 = -0.083097205;
                }
            } else {
                if (input[8] < 33.0) {
                    var3 = -0.1985351;
                } else {
                    var3 = 0.20411839;
                }
            }
        } else {
            if (input[3] < 0.00058559206) {
                if (input[8] < 187.0) {
                    var3 = 0.027940564;
                } else {
                    var3 = 0.21270151;
                }
            } else {
                if (input[1] < 47.0) {
                    var3 = -0.23170497;
                } else {
                    var3 = -0.16400051;
                }
            }
        }
    }
    double var4;
    if (input[9] < 6.0) {
        if (input[3] < 0.026008183) {
            if (input[8] < 29.0) {
                var4 = 0.21173933;
            } else {
                if (input[8] < 32.0) {
                    var4 = -0.3296517;
                } else {
                    var4 = 0.22344492;
                }
            }
        } else {
            if (input[3] < 0.10909091) {
                if (input[6] < 13.0) {
                    var4 = -0.15725715;
                } else {
                    var4 = 0.08929305;
                }
            } else {
                if (input[8] < 3.0) {
                    var4 = 0.1322556;
                } else {
                    var4 = 0.21371754;
                }
            }
        }
    } else {
        if (input[9] < 7.0) {
            if (input[1] < 323.0) {
                if (input[3] < 0.02259887) {
                    var4 = 0.21266761;
                } else {
                    var4 = -0.045103543;
                }
            } else {
                if (input[8] < 33.0) {
                    var4 = -0.18311976;
                } else {
                    var4 = 0.21719708;
                }
            }
        } else {
            if (input[4] < 0.003562341) {
                if (input[3] < 0.00058559206) {
                    var4 = 0.101465166;
                } else {
                    var4 = -0.18125679;
                }
            } else {
                if (input[9] < 8.0) {
                    var4 = -0.12952125;
                } else {
                    var4 = 0.059281938;
                }
            }
        }
    }
    double var5;
    if (input[1] < 13.0) {
        if (input[3] < 0.125) {
            if (input[4] < 0.0003362915) {
                var5 = 0.2002345;
            } else {
                if (input[3] < 0.102564104) {
                    var5 = -0.18303208;
                } else {
                    var5 = 0.14063731;
                }
            }
        } else {
            if (input[3] < 0.16666667) {
                if (input[4] < 0.0003362915) {
                    var5 = -0.03192163;
                } else {
                    var5 = 0.15662691;
                }
            } else {
                if (input[0] < 6.0) {
                    var5 = 0.13806796;
                } else {
                    var5 = 0.18327586;
                }
            }
        }
    } else {
        if (input[4] < 0.0034864573) {
            if (input[2] < 3.6249003) {
                if (input[4] < 0.0003362915) {
                    var5 = -0.10670704;
                } else {
                    var5 = 0.10233535;
                }
            } else {
                if (input[1] < 821.0) {
                    var5 = -0.023414912;
                } else {
                    var5 = -0.18302548;
                }
            }
        } else {
            if (input[0] < 230.0) {
                if (input[4] < 0.0045634923) {
                    var5 = 0.058771215;
                } else {
                    var5 = 0.19451329;
                }
            } else {
                if (input[4] < 0.0062896824) {
                    var5 = 0.032263197;
                } else {
                    var5 = -0.18535107;
                }
            }
        }
    }
    double var6;
    if (input[9] < 6.0) {
        if (input[3] < 0.026008183) {
            var6 = 0.19217166;
        } else {
            if (input[8] < 8.0) {
                if (input[8] < 3.0) {
                    var6 = 0.046028797;
                } else {
                    var6 = 0.16606057;
                }
            } else {
                var6 = -0.288797;
            }
        }
    } else {
        if (input[9] < 7.0) {
            if (input[2] < 3.329897) {
                if (input[3] < 0.024198428) {
                    var6 = 0.16171458;
                } else {
                    var6 = -0.04608834;
                }
            } else {
                if (input[8] < 33.0) {
                    var6 = -0.15795067;
                } else {
                    var6 = 0.17365533;
                }
            }
        } else {
            if (input[1] < 47.0) {
                if (input[2] < 2.7) {
                    var6 = -0.2019816;
                } else {
                    var6 = 0.00015880086;
                }
            } else {
                if (input[2] < 3.319149) {
                    var6 = -0.01343524;
                } else {
                    var6 = -0.15373333;
                }
            }
        }
    }
    double var7;
    if (input[9] < 6.0) {
        if (input[3] < 0.026948052) {
            if (input[8] < 29.0) {
                var7 = 0.18674673;
            } else {
                if (input[8] < 32.0) {
                    var7 = -0.32498387;
                } else {
                    var7 = 0.19854221;
                }
            }
        } else {
            if (input[8] < 8.0) {
                if (input[8] < 3.0) {
                    var7 = 0.03718479;
                } else {
                    var7 = 0.1537744;
                }
            } else {
                var7 = -0.27044398;
            }
        }
    } else {
        if (input[3] < 0.033868093) {
            if (input[2] < 3.329897) {
                if (input[1] < 144.0) {
                    var7 = -0.046936154;
                } else {
                    var7 = 0.14435707;
                }
            } else {
                if (input[3] < 0.00058559206) {
                    var7 = 0.16178714;
                } else {
                    var7 = -0.14814109;
                }
            }
        } else {
            if (input[0] < 18.0) {
                var7 = 0.18744846;
            } else {
                if (input[8] < 7.0) {
                    var7 = -0.18722382;
                } else {
                    var7 = 0.043493677;
                }
            }
        }
    }
    double var8;
    if (input[9] < 6.0) {
        if (input[3] < 0.025118984) {
            if (input[8] < 29.0) {
                var8 = 0.1812668;
            } else {
                if (input[8] < 32.0) {
                    var8 = -0.25339186;
                } else {
                    var8 = 0.18896048;
                }
            }
        } else {
            if (input[3] < 0.10909091) {
                if (input[0] < 13.0) {
                    var8 = -0.13864917;
                } else {
                    var8 = 0.059031326;
                }
            } else {
                if (input[3] < 0.11818182) {
                    var8 = 0.17669332;
                } else {
                    var8 = 0.09489426;
                }
            }
        }
    } else {
        if (input[3] < 0.033868093) {
            if (input[2] < 3.244392) {
                if (input[9] < 11.0) {
                    var8 = 0.11424847;
                } else {
                    var8 = -0.087352976;
                }
            } else {
                if (input[3] < 0.00058559206) {
                    var8 = 0.14541991;
                } else {
                    var8 = -0.13143909;
                }
            }
        } else {
            if (input[9] < 7.0) {
                if (input[2] < 2.08) {
                    var8 = -0.122536115;
                } else {
                    var8 = 0.18533264;
                }
            } else {
                if (input[2] < 2.7555556) {
                    var8 = -0.18564932;
                } else {
                    var8 = -0.092970215;
                }
            }
        }
    }
    double var9;
    if (input[1] < 13.0) {
        if (input[3] < 0.125) {
            if (input[4] < 0.0003362915) {
                var9 = 0.17602079;
            } else {
                if (input[3] < 0.102564104) {
                    var9 = -0.16962574;
                } else {
                    var9 = 0.11256354;
                }
            }
        } else {
            if (input[3] < 0.16666667) {
                if (input[1] < 8.0) {
                    var9 = -0.16064376;
                } else {
                    var9 = 0.014760794;
                }
            } else {
                if (input[0] < 6.0) {
                    var9 = 0.10524629;
                } else {
                    var9 = 0.15709849;
                }
            }
        }
    } else {
        if (input[4] < 0.011496464) {
            if (input[2] < 3.6249003) {
                if (input[4] < 0.0003362915) {
                    var9 = -0.08214289;
                } else {
                    var9 = 0.050825354;
                }
            } else {
                if (input[1] < 5692.0) {
                    var9 = -0.13875796;
                } else {
                    var9 = 0.10537121;
                }
            }
        } else {
            if (input[8] < 26.0) {
                if (input[4] < 0.013038549) {
                    var9 = 0.07131989;
                } else {
                    var9 = 0.18295783;
                }
            } else {
                if (input[2] < 3.4146342) {
                    var9 = -0.11855534;
                } else {
                    var9 = 0.042075984;
                }
            }
        }
    }
    double var10;
    if (input[9] < 6.0) {
        if (input[5] < 0.00001) {
            var10 = 0.17205094;
        } else {
            if (input[8] < 3.0) {
                if (input[2] < 2.1176472) {
                    var10 = 0.09290334;
                } else {
                    var10 = -0.042733032;
                }
            } else {
                if (input[8] < 4.0) {
                    var10 = 0.15841584;
                } else {
                    var10 = 0.097509354;
                }
            }
        }
    } else {
        if (input[1] < 47.0) {
            if (input[6] < 18.0) {
                var10 = 0.17346363;
            } else {
                if (input[2] < 2.7) {
                    var10 = -0.17283764;
                } else {
                    var10 = 0.04654087;
                }
            }
        } else {
            if (input[2] < 3.329897) {
                if (input[1] < 138.0) {
                    var10 = -0.06838843;
                } else {
                    var10 = 0.12506448;
                }
            } else {
                if (input[1] < 5692.0) {
                    var10 = -0.12380042;
                } else {
                    var10 = 0.12847748;
                }
            }
        }
    }
    double var11;
    if (input[1] < 13.0) {
        if (input[3] < 0.11111111) {
            if (input[4] < 0.0003362915) {
                var11 = 0.16946258;
            } else {
                var11 = -0.06662667;
            }
        } else {
            if (input[3] < 0.16666667) {
                if (input[0] < 9.0) {
                    var11 = -0.066878274;
                } else {
                    var11 = 0.119146205;
                }
            } else {
                if (input[0] < 6.0) {
                    var11 = 0.08549886;
                } else {
                    var11 = 0.14224252;
                }
            }
        }
    } else {
        if (input[4] < 0.01144816) {
            if (input[1] < 2078.0) {
                if (input[4] < 0.0003362915) {
                    var11 = -0.072049625;
                } else {
                    var11 = 0.048669364;
                }
            } else {
                if (input[0] < 1507.0) {
                    var11 = -0.15603323;
                } else {
                    var11 = -0.005538122;
                }
            }
        } else {
            if (input[8] < 26.0) {
                if (input[4] < 0.013038549) {
                    var11 = 0.0872135;
                } else {
                    var11 = 0.1707342;
                }
            } else {
                if (input[3] < 0.006525396) {
                    var11 = 0.037592396;
                } else {
                    var11 = -0.080572754;
                }
            }
        }
    }
    double var12;
    if (input[9] < 6.0) {
        if (input[3] < 0.026008183) {
            if (input[8] < 29.0) {
                var12 = 0.16942784;
            } else {
                if (input[8] < 32.0) {
                    var12 = -0.25400254;
                } else {
                    var12 = 0.17993629;
                }
            }
        } else {
            if (input[8] < 6.0) {
                if (input[1] < 22.0) {
                    var12 = 0.02735041;
                } else {
                    var12 = 0.165381;
                }
            } else {
                if (input[9] < 4.0) {
                    var12 = 0.031871032;
                } else {
                    var12 = -0.22259042;
                }
            }
        }
    } else {
        if (input[3] < 0.025118984) {
            if (input[2] < 3.244392) {
                if (input[9] < 11.0) {
                    var12 = 0.14460137;
                } else {
                    var12 = -0.09278518;
                }
            } else {
                if (input[8] < 24.0) {
                    var12 = 0.04829643;
                } else {
                    var12 = -0.11116981;
                }
            }
        } else {
            if (input[9] < 11.0) {
                if (input[3] < 0.07083333) {
                    var12 = -0.15856086;
                } else {
                    var12 = 0.11227009;
                }
            } else {
                if (input[8] < 13.0) {
                    var12 = 0.3600354;
                } else {
                    var12 = -0.099079005;
                }
            }
        }
    }
    double var13;
    if (input[9] < 6.0) {
        if (input[3] < 0.025118984) {
            if (input[8] < 29.0) {
                var13 = 0.16603215;
            } else {
                if (input[8] < 32.0) {
                    var13 = -0.2316047;
                } else {
                    var13 = 0.17261498;
                }
            }
        } else {
            if (input[8] < 10.0) {
                if (input[0] < 19.0) {
                    var13 = 0.019437173;
                } else {
                    var13 = 0.13124202;
                }
            } else {
                var13 = -0.2170025;
            }
        }
    } else {
        if (input[3] < 0.024296675) {
            if (input[2] < 3.244392) {
                if (input[9] < 11.0) {
                    var13 = 0.13350768;
                } else {
                    var13 = -0.0762474;
                }
            } else {
                if (input[9] < 30.0) {
                    var13 = -0.103081234;
                } else {
                    var13 = 0.048624095;
                }
            }
        } else {
            if (input[9] < 11.0) {
                if (input[0] < 17.0) {
                    var13 = 0.13262461;
                } else {
                    var13 = -0.15026954;
                }
            } else {
                if (input[8] < 13.0) {
                    var13 = 0.30031386;
                } else {
                    var13 = -0.08402947;
                }
            }
        }
    }
    double var14;
    if (input[9] < 6.0) {
        if (input[5] < 0.00001) {
            var14 = 0.16278137;
        } else {
            if (input[4] < 0.0003362915) {
                if (input[1] < 13.0) {
                    var14 = 0.07881916;
                } else {
                    var14 = -0.0050574113;
                }
            } else {
                if (input[1] < 12.0) {
                    var14 = 0.031540573;
                } else {
                    var14 = 0.1382128;
                }
            }
        }
    } else {
        if (input[4] < 0.0003362915) {
            if (input[8] < 41.0) {
                if (input[9] < 7.0) {
                    var14 = -0.029325416;
                } else {
                    var14 = -0.12663637;
                }
            } else {
                var14 = 0.2339517;
            }
        } else {
            if (input[2] < 3.329897) {
                if (input[0] < 94.0) {
                    var14 = -0.053524308;
                } else {
                    var14 = 0.1685516;
                }
            } else {
                if (input[8] < 25.0) {
                    var14 = 0.24014983;
                } else {
                    var14 = -0.08898568;
                }
            }
        }
    }
    double var15;
    if (input[9] < 6.0) {
        if (input[3] < 0.025118984) {
            if (input[8] < 29.0) {
                var15 = 0.16282542;
            } else {
                if (input[8] < 32.0) {
                    var15 = -0.22107287;
                } else {
                    var15 = 0.16657446;
                }
            }
        } else {
            if (input[8] < 6.0) {
                if (input[0] < 19.0) {
                    var15 = 0.01559942;
                } else {
                    var15 = 0.14169379;
                }
            } else {
                if (input[9] < 4.0) {
                    var15 = -0.013703503;
                } else {
                    var15 = -0.18141288;
                }
            }
        }
    } else {
        if (input[3] < 0.033868093) {
            if (input[9] < 12.0) {
                if (input[1] < 2078.0) {
                    var15 = 0.033710126;
                } else {
                    var15 = -0.091579705;
                }
            } else {
                if (input[9] < 31.0) {
                    var15 = -0.1487511;
                } else {
                    var15 = 0.034404017;
                }
            }
        } else {
            if (input[9] < 7.0) {
                if (input[0] < 21.0) {
                    var15 = 0.0059424653;
                } else {
                    var15 = 0.29925576;
                }
            } else {
                if (input[9] < 8.0) {
                    var15 = -0.15034331;
                } else {
                    var15 = 0.071211316;
                }
            }
        }
    }
    double var16;
    if (input[1] < 13.0) {
        if (input[3] < 0.11111111) {
            if (input[4] < 0.0003362915) {
                var16 = 0.1599712;
            } else {
                var16 = -0.10260649;
            }
        } else {
            if (input[3] < 0.16666667) {
                if (input[9] < 3.0) {
                    var16 = -0.06356383;
                } else {
                    var16 = 0.15820825;
                }
            } else {
                if (input[0] < 5.0) {
                    var16 = 0.04144523;
                } else {
                    var16 = 0.100393444;
                }
            }
        }
    } else {
        if (input[9] < 7.0) {
            if (input[0] < 13.0) {
                if (input[8] < 3.0) {
                    var16 = -0.15531711;
                } else {
                    var16 = 0.113701284;
                }
            } else {
                if (input[1] < 16.0) {
                    var16 = 0.2644428;
                } else {
                    var16 = 0.012529782;
                }
            }
        } else {
            if (input[3] < 0.014692918) {
                if (input[1] < 1995.0) {
                    var16 = 0.049956962;
                } else {
                    var16 = -0.07193568;
                }
            } else {
                if (input[1] < 39.0) {
                    var16 = -0.15514363;
                } else {
                    var16 = -0.09572411;
                }
            }
        }
    }
    double var17;
    if (input[0] < 8.0) {
        if (input[3] < 0.2) {
            if (input[0] < 7.0) {
                var17 = 0.1567935;
            } else {
                if (input[2] < 1.75) {
                    var17 = -0.082963765;
                } else {
                    var17 = 0.12536165;
                }
            }
        } else {
            if (input[0] < 5.0) {
                if (input[0] < 4.0) {
                    var17 = 0.09424025;
                } else {
                    var17 = 0.038013477;
                }
            } else {
                var17 = 0.07018837;
            }
        }
    } else {
        if (input[4] < 0.01144816) {
            if (input[8] < 187.0) {
                if (input[2] < 3.6795666) {
                    var17 = -0.019216709;
                } else {
                    var17 = -0.10738904;
                }
            } else {
                if (input[8] < 209.0) {
                    var17 = 0.05796297;
                } else {
                    var17 = 0.1968842;
                }
            }
        } else {
            if (input[2] < 2.08) {
                if (input[4] < 0.035714287) {
                    var17 = -0.09011421;
                } else {
                    var17 = 0.11938893;
                }
            } else {
                if (input[8] < 26.0) {
                    var17 = 0.14273494;
                } else {
                    var17 = -0.041976497;
                }
            }
        }
    }
    double var18;
    if (input[3] < 0.000867642) {
        if (input[9] < 16.0) {
            if (input[9] < 7.0) {
                var18 = 0.15545936;
            } else {
                var18 = 0.29735142;
            }
        } else {
            if (input[4] < 0.0014034595) {
                if (input[4] < 0.0011527161) {
                    var18 = 0.0044636875;
                } else {
                    var18 = -0.17954919;
                }
            } else {
                if (input[1] < 5692.0) {
                    var18 = -0.040516764;
                } else {
                    var18 = 0.21075785;
                }
            }
        }
    } else {
        if (input[9] < 7.0) {
            if (input[8] < 33.0) {
                if (input[8] < 26.0) {
                    var18 = 0.03431196;
                } else {
                    var18 = -0.104316756;
                }
            } else {
                var18 = 0.18395191;
            }
        } else {
            if (input[3] < 0.014692918) {
                if (input[2] < 3.6249003) {
                    var18 = 0.051489137;
                } else {
                    var18 = -0.09521564;
                }
            } else {
                if (input[1] < 39.0) {
                    var18 = -0.14845623;
                } else {
                    var18 = -0.08165054;
                }
            }
        }
    }
    double var19;
    if (input[5] < 0.00001) {
        var19 = 0.15258579;
    } else {
        if (input[9] < 7.0) {
            if (input[1] < 19.0) {
                if (input[0] < 15.0) {
                    var19 = 0.030766198;
                } else {
                    var19 = -0.14483534;
                }
            } else {
                if (input[8] < 8.0) {
                    var19 = 0.112155065;
                } else {
                    var19 = -0.002546661;
                }
            }
        } else {
            if (input[1] < 47.0) {
                if (input[9] < 8.0) {
                    var19 = -0.15058276;
                } else {
                    var19 = 0.13221702;
                }
            } else {
                if (input[1] < 49.0) {
                    var19 = 0.5845783;
                } else {
                    var19 = -0.030743664;
                }
            }
        }
    }
    double var20;
    if (input[3] < 0.00058559206) {
        if (input[2] < 3.9) {
            var20 = 0.15636921;
        } else {
            if (input[4] < 0.0013317748) {
                var20 = -0.11333782;
            } else {
                var20 = 0.17186357;
            }
        }
    } else {
        if (input[9] < 13.0) {
            if (input[0] < 1507.0) {
                if (input[1] < 2078.0) {
                    var20 = 0.009461908;
                } else {
                    var20 = -0.10971953;
                }
            } else {
                if (input[8] < 100.0) {
                    var20 = 0.51209587;
                } else {
                    var20 = 0.037037347;
                }
            }
        } else {
            if (input[9] < 31.0) {
                if (input[8] < 22.0) {
                    var20 = 0.012751217;
                } else {
                    var20 = -0.1537402;
                }
            } else {
                if (input[8] < 62.0) {
                    var20 = -0.13776082;
                } else {
                    var20 = 0.11080669;
                }
            }
        }
    }
    double var21;
    if (input[3] < 0.00058559206) {
        if (input[2] < 3.9) {
            var21 = 0.15474628;
        } else {
            if (input[1] < 8496.0) {
                var21 = -0.116254725;
            } else {
                if (input[2] < 3.956044) {
                    var21 = 0.027219668;
                } else {
                    var21 = 0.14943263;
                }
            }
        }
    } else {
        if (input[9] < 12.0) {
            if (input[2] < 3.7372549) {
                if (input[2] < 3.681081) {
                    var21 = 0.0052869045;
                } else {
                    var21 = -0.14435448;
                }
            } else {
                if (input[1] < 2860.0) {
                    var21 = 0.2368696;
                } else {
                    var21 = 0.029232396;
                }
            }
        } else {
            if (input[3] < 0.0012313456) {
                if (input[2] < 3.6880598) {
                    var21 = 0.10424526;
                } else {
                    var21 = -0.09471019;
                }
            } else {
                if (input[8] < 22.0) {
                    var21 = -0.033250544;
                } else {
                    var21 = -0.1571599;
                }
            }
        }
    }
    double var22;
    if (input[3] < 0.000867642) {
        if (input[9] < 16.0) {
            var22 = 0.15827724;
        } else {
            if (input[3] < 0.00058559206) {
                if (input[2] < 3.9) {
                    var22 = 0.18919556;
                } else {
                    var22 = 0.050317258;
                }
            } else {
                if (input[8] < 117.0) {
                    var22 = 0.061000932;
                } else {
                    var22 = -0.1107725;
                }
            }
        }
    } else {
        if (input[9] < 12.0) {
            if (input[3] < 0.024296675) {
                if (input[2] < 3.3117409) {
                    var22 = 0.09680635;
                } else {
                    var22 = -0.021559445;
                }
            } else {
                if (input[3] < 0.079166666) {
                    var22 = -0.06321237;
                } else {
                    var22 = 0.030755924;
                }
            }
        } else {
            if (input[3] < 0.0012313456) {
                if (input[2] < 3.6880598) {
                    var22 = 0.10955117;
                } else {
                    var22 = -0.104499534;
                }
            } else {
                if (input[8] < 22.0) {
                    var22 = -0.0018148962;
                } else {
                    var22 = -0.15120043;
                }
            }
        }
    }
    double var23;
    if (input[3] < 0.0004504355) {
        var23 = 0.14419293;
    } else {
        if (input[9] < 6.0) {
            if (input[3] < 0.075) {
                if (input[2] < 2.0) {
                    var23 = -0.2128123;
                } else {
                    var23 = 0.093622096;
                }
            } else {
                if (input[3] < 0.079166666) {
                    var23 = -0.18294396;
                } else {
                    var23 = 0.028450975;
                }
            }
        } else {
            if (input[3] < 0.02259887) {
                if (input[2] < 3.3117409) {
                    var23 = 0.058129907;
                } else {
                    var23 = -0.044531822;
                }
            } else {
                if (input[9] < 11.0) {
                    var23 = -0.10824391;
                } else {
                    var23 = 0.08163022;
                }
            }
        }
    }
    double var24;
    if (input[3] < 0.000867642) {
        if (input[8] < 116.0) {
            if (input[4] < 0.0010139599) {
                var24 = 0.13861;
            } else {
                var24 = 0.28517753;
            }
        } else {
            if (input[8] < 182.0) {
                if (input[3] < 0.00058559206) {
                    var24 = 0.046736762;
                } else {
                    var24 = -0.10762618;
                }
            } else {
                var24 = 0.16013126;
            }
        }
    } else {
        if (input[4] < 0.013038549) {
            if (input[1] < 13.0) {
                if (input[1] < 10.0) {
                    var24 = 0.012943317;
                } else {
                    var24 = 0.1505011;
                }
            } else {
                if (input[6] < 13.0) {
                    var24 = -0.14924286;
                } else {
                    var24 = -0.007542055;
                }
            }
        } else {
            if (input[1] < 12.0) {
                if (input[1] < 11.0) {
                    var24 = 0.12524693;
                } else {
                    var24 = -0.1621048;
                }
            } else {
                if (input[3] < 0.06140351) {
                    var24 = 0.076973945;
                } else {
                    var24 = 0.1756992;
                }
            }
        }
    }
    double var25;
    if (input[3] < 0.000867642) {
        if (input[9] < 16.0) {
            var25 = 0.14998323;
        } else {
            if (input[4] < 0.0014034595) {
                if (input[4] < 0.0011527161) {
                    var25 = -0.03249495;
                } else {
                    var25 = -0.11367616;
                }
            } else {
                if (input[3] < 0.00058559206) {
                    var25 = 0.16708478;
                } else {
                    var25 = 0.005227708;
                }
            }
        }
    } else {
        if (input[9] < 13.0) {
            if (input[4] < 0.0003362915) {
                if (input[3] < 0.079166666) {
                    var25 = -0.041743856;
                } else {
                    var25 = 0.021340411;
                }
            } else {
                if (input[8] < 26.0) {
                    var25 = 0.102750935;
                } else {
                    var25 = -0.0136343725;
                }
            }
        } else {
            if (input[9] < 31.0) {
                if (input[8] < 22.0) {
                    var25 = -0.0009053952;
                } else {
                    var25 = -0.14319025;
                }
            } else {
                if (input[8] < 60.0) {
                    var25 = -0.12074484;
                } else {
                    var25 = 0.09817752;
                }
            }
        }
    }
    double var26;
    if (input[5] < 0.00001) {
        var26 = 0.14127445;
    } else {
        if (input[4] < 0.01172043) {
            if (input[4] < 0.010373885) {
                if (input[9] < 7.0) {
                    var26 = 0.0152496025;
                } else {
                    var26 = -0.028095584;
                }
            } else {
                if (input[4] < 0.01144816) {
                    var26 = -0.15660712;
                } else {
                    var26 = 0.017846368;
                }
            }
        } else {
            if (input[2] < 2.08) {
                if (input[4] < 0.035714287) {
                    var26 = -0.08761084;
                } else {
                    var26 = 0.104057215;
                }
            } else {
                if (input[0] < 20.0) {
                    var26 = 0.1665272;
                } else {
                    var26 = 0.0792448;
                }
            }
        }
    }
    double var27;
    if (input[3] < 0.0004504355) {
        var27 = 0.13629934;
    } else {
        if (input[4] < 0.0003362915) {
            if (input[2] < 2.5636363) {
                if (input[8] < 3.0) {
                    var27 = -0.02285122;
                } else {
                    var27 = 0.071513705;
                }
            } else {
                if (input[1] < 117.0) {
                    var27 = -0.10597893;
                } else {
                    var27 = -0.0058758063;
                }
            }
        } else {
            if (input[4] < 0.0026074378) {
                if (input[1] < 2078.0) {
                    var27 = 0.17499661;
                } else {
                    var27 = 0.023613304;
                }
            } else {
                if (input[8] < 26.0) {
                    var27 = 0.070576265;
                } else {
                    var27 = -0.07843879;
                }
            }
        }
    }
    double var28;
    if (input[3] < 0.0010299477) {
        if (input[8] < 78.0) {
            if (input[1] < 3.0) {
                var28 = 0.12857592;
            } else {
                var28 = 0.39584953;
            }
        } else {
            if (input[9] < 16.0) {
                var28 = 0.17347346;
            } else {
                if (input[1] < 5692.0) {
                    var28 = -0.09000337;
                } else {
                    var28 = 0.044607386;
                }
            }
        }
    } else {
        if (input[9] < 12.0) {
            if (input[9] < 8.0) {
                if (input[9] < 7.0) {
                    var28 = 0.006483132;
                } else {
                    var28 = -0.09088093;
                }
            } else {
                if (input[2] < 3.6115658) {
                    var28 = 0.123569466;
                } else {
                    var28 = -0.06956833;
                }
            }
        } else {
            if (input[3] < 0.0012313456) {
                if (input[6] < 1524.0) {
                    var28 = 0.21951503;
                } else {
                    var28 = -0.06915679;
                }
            } else {
                if (input[8] < 22.0) {
                    var28 = -0.0058574905;
                } else {
                    var28 = -0.13654475;
                }
            }
        }
    }
    double var29;
    if (input[0] < 8.0) {
        if (input[5] < 0.00001) {
            var29 = 0.12437932;
        } else {
            if (input[1] < 7.0) {
                if (input[0] < 7.0) {
                    var29 = 0.03137014;
                } else {
                    var29 = -0.12385307;
                }
            } else {
                var29 = 0.093643725;
            }
        }
    } else {
        if (input[2] < 2.142857) {
            if (input[2] < 2.1333334) {
                if (input[0] < 23.0) {
                    var29 = -0.022722507;
                } else {
                    var29 = 0.17577071;
                }
            } else {
                var29 = -0.19375844;
            }
        } else {
            if (input[2] < 2.16) {
                if (input[9] < 3.0) {
                    var29 = -0.013375862;
                } else {
                    var29 = 0.24474789;
                }
            } else {
                if (input[1] < 603.0) {
                    var29 = -0.019718422;
                } else {
                    var29 = 0.04439477;
                }
            }
        }
    }
    double var30;
    if (input[3] < 0.000867642) {
        if (input[9] < 16.0) {
            var30 = 0.14636165;
        } else {
            if (input[4] < 0.002630761) {
                if (input[8] < 178.0) {
                    var30 = -0.027135078;
                } else {
                    var30 = -0.15980506;
                }
            } else {
                var30 = 0.14056697;
            }
        }
    } else {
        if (input[9] < 13.0) {
            if (input[1] < 548.0) {
                if (input[6] < 230.0) {
                    var30 = 0.001143163;
                } else {
                    var30 = -0.12067009;
                }
            } else {
                if (input[1] < 2078.0) {
                    var30 = 0.14278296;
                } else {
                    var30 = -0.05281372;
                }
            }
        } else {
            if (input[9] < 31.0) {
                if (input[4] < 0.004369942) {
                    var30 = -0.12850489;
                } else {
                    var30 = 0.008434152;
                }
            } else {
                if (input[8] < 60.0) {
                    var30 = -0.10310659;
                } else {
                    var30 = 0.078350864;
                }
            }
        }
    }
    double var31;
    if (input[3] < 0.0010299477) {
        if (input[8] < 78.0) {
            if (input[0] < 4.0) {
                var31 = 0.11464346;
            } else {
                var31 = 0.29418132;
            }
        } else {
            if (input[9] < 16.0) {
                var31 = 0.17827329;
            } else {
                if (input[3] < 0.00058559206) {
                    var31 = 0.048941735;
                } else {
                    var31 = -0.08337454;
                }
            }
        }
    } else {
        if (input[9] < 12.0) {
            if (input[2] < 3.7372549) {
                if (input[2] < 3.681081) {
                    var31 = 0.0037772816;
                } else {
                    var31 = -0.13699819;
                }
            } else {
                if (input[4] < 0.002554674) {
                    var31 = 0.35182086;
                } else {
                    var31 = 0.02196032;
                }
            }
        } else {
            if (input[3] < 0.0012313456) {
                if (input[4] < 0.0024467446) {
                    var31 = 0.11338311;
                } else {
                    var31 = -0.062671155;
                }
            } else {
                if (input[8] < 22.0) {
                    var31 = 0.0005787394;
                } else {
                    var31 = -0.12581176;
                }
            }
        }
    }
    double var32;
    if (input[3] < 0.0032132731) {
        if (input[6] < 1107.0) {
            if (input[9] < 12.0) {
                if (input[8] < 27.0) {
                    var32 = 0.106929086;
                } else {
                    var32 = 0.24869226;
                }
            } else {
                var32 = -0.010678521;
            }
        } else {
            if (input[6] < 1507.0) {
                if (input[4] < 0.0025653031) {
                    var32 = 0.007222309;
                } else {
                    var32 = -0.14155835;
                }
            } else {
                if (input[9] < 14.0) {
                    var32 = 0.23833649;
                } else {
                    var32 = 0.0056252903;
                }
            }
        }
    } else {
        if (input[8] < 26.0) {
            if (input[4] < 0.0003362915) {
                if (input[9] < 7.0) {
                    var32 = 0.0005121178;
                } else {
                    var32 = -0.06525053;
                }
            } else {
                if (input[6] < 94.0) {
                    var32 = 0.010462025;
                } else {
                    var32 = 0.16525206;
                }
            }
        } else {
            if (input[4] < 0.006071279) {
                if (input[4] < 0.0058662207) {
                    var32 = -0.042475574;
                } else {
                    var32 = 0.48399797;
                }
            } else {
                if (input[8] < 32.0) {
                    var32 = -0.17580062;
                } else {
                    var32 = 0.047289707;
                }
            }
        }
    }
    double var33;
    if (input[3] < 0.0032132731) {
        if (input[0] < 1107.0) {
            if (input[0] < 756.0) {
                if (input[2] < 3.4320989) {
                    var33 = 0.17400476;
                } else {
                    var33 = -0.02284908;
                }
            } else {
                var33 = 0.3343596;
            }
        } else {
            if (input[0] < 1507.0) {
                if (input[2] < 3.6512642) {
                    var33 = 0.0009584361;
                } else {
                    var33 = -0.11352296;
                }
            } else {
                if (input[9] < 16.0) {
                    var33 = 0.18024698;
                } else {
                    var33 = 0.009107574;
                }
            }
        }
    } else {
        if (input[8] < 26.0) {
            if (input[3] < 0.02259887) {
                if (input[8] < 15.0) {
                    var33 = 0.0068865116;
                } else {
                    var33 = 0.14512874;
                }
            } else {
                if (input[8] < 10.0) {
                    var33 = 0.0008073892;
                } else {
                    var33 = -0.19110523;
                }
            }
        } else {
            if (input[2] < 3.5872502) {
                if (input[3] < 0.0076621473) {
                    var33 = -0.14844573;
                } else {
                    var33 = -0.023522336;
                }
            } else {
                if (input[3] < 0.0039862623) {
                    var33 = -0.14929023;
                } else {
                    var33 = 0.21300071;
                }
            }
        }
    }
    double var34;
    if (input[4] < 0.04090909) {
        if (input[3] < 0.09848485) {
            if (input[1] < 16.0) {
                if (input[9] < 3.0) {
                    var34 = 0.10111489;
                } else {
                    var34 = 0.2174746;
                }
            } else {
                if (input[1] < 17.0) {
                    var34 = -0.13214049;
                } else {
                    var34 = 0.0030036515;
                }
            }
        } else {
            if (input[3] < 0.10909091) {
                if (input[9] < 4.0) {
                    var34 = -0.15989462;
                } else {
                    var34 = 0.18010826;
                }
            } else {
                if (input[3] < 0.11818182) {
                    var34 = 0.13593999;
                } else {
                    var34 = -0.0027625482;
                }
            }
        }
    } else {
        var34 = 0.15816204;
    }
    double var35;
    if (input[4] < 0.04090909) {
        if (input[3] < 0.0032132731) {
            if (input[0] < 1107.0) {
                if (input[4] < 0.003587338) {
                    var35 = 0.18976462;
                } else {
                    var35 = 0.039849855;
                }
            } else {
                if (input[8] < 64.0) {
                    var35 = -0.071684025;
                } else {
                    var35 = 0.035714403;
                }
            }
        } else {
            if (input[9] < 7.0) {
                if (input[3] < 0.075) {
                    var35 = 0.03853715;
                } else {
                    var35 = -0.014178769;
                }
            } else {
                if (input[2] < 2.7555556) {
                    var35 = -0.106539726;
                } else {
                    var35 = 0.010379622;
                }
            }
        }
    } else {
        var35 = 0.15113339;
    }
    double var36;
    if (input[0] < 8.0) {
        if (input[3] < 0.2) {
            if (input[0] < 7.0) {
                var36 = 0.09880375;
            } else {
                if (input[2] < 1.75) {
                    var36 = -0.07818376;
                } else {
                    var36 = 0.07577785;
                }
            }
        } else {
            if (input[0] < 5.0) {
                var36 = 0.024554681;
            } else {
                var36 = 0.037451115;
            }
        }
    } else {
        if (input[0] < 13.0) {
            if (input[8] < 3.0) {
                if (input[4] < 0.035714287) {
                    var36 = -0.11372517;
                } else {
                    var36 = 0.13125566;
                }
            } else {
                if (input[9] < 3.0) {
                    var36 = -0.14466478;
                } else {
                    var36 = 0.1785274;
                }
            }
        } else {
            if (input[3] < 0.079166666) {
                if (input[3] < 0.07619048) {
                    var36 = 0.005581276;
                } else {
                    var36 = -0.15745956;
                }
            } else {
                if (input[2] < 2.275862) {
                    var36 = 0.20551783;
                } else {
                    var36 = 0.0853449;
                }
            }
        }
    }
    double var37;
    if (input[4] < 0.02) {
        if (input[1] < 13.0) {
            if (input[3] < 0.11111111) {
                if (input[0] < 12.0) {
                    var37 = 0.1273525;
                } else {
                    var37 = 0.03562745;
                }
            } else {
                if (input[3] < 0.16666667) {
                    var37 = -0.03628514;
                } else {
                    var37 = 0.035561536;
                }
            }
        } else {
            if (input[0] < 13.0) {
                if (input[2] < 2.3428571) {
                    var37 = -0.1350006;
                } else {
                    var37 = -0.02019649;
                }
            } else {
                if (input[1] < 16.0) {
                    var37 = 0.18067728;
                } else {
                    var37 = -0.009190461;
                }
            }
        }
    } else {
        if (input[1] < 12.0) {
            if (input[0] < 11.0) {
                var37 = 0.09070218;
            } else {
                var37 = -0.138672;
            }
        } else {
            var37 = 0.136102;
        }
    }
    double var38;
    if (input[9] < 13.0) {
        if (input[9] < 8.0) {
            if (input[9] < 7.0) {
                if (input[3] < 0.075) {
                    var38 = 0.03428866;
                } else {
                    var38 = -0.015927786;
                }
            } else {
                if (input[2] < 2.7555556) {
                    var38 = -0.14036828;
                } else {
                    var38 = -0.0032689474;
                }
            }
        } else {
            if (input[2] < 3.6115658) {
                if (input[1] < 229.0) {
                    var38 = 0.016129952;
                } else {
                    var38 = 0.17578971;
                }
            } else {
                if (input[1] < 2579.0) {
                    var38 = -0.077475816;
                } else {
                    var38 = 0.10739966;
                }
            }
        }
    } else {
        if (input[9] < 31.0) {
            if (input[1] < 3316.0) {
                if (input[2] < 3.2181208) {
                    var38 = -0.01873515;
                } else {
                    var38 = -0.13781603;
                }
            } else {
                if (input[9] < 16.0) {
                    var38 = 0.1107319;
                } else {
                    var38 = -0.09209028;
                }
            }
        } else {
            if (input[4] < 0.0019058975) {
                if (input[4] < 0.0012893142) {
                    var38 = -0.020895455;
                } else {
                    var38 = -0.09996903;
                }
            } else {
                if (input[3] < 0.0012038221) {
                    var38 = 0.018013738;
                } else {
                    var38 = 0.23801574;
                }
            }
        }
    }
    double var39;
    if (input[4] < 0.01144816) {
        if (input[4] < 0.010373885) {
            if (input[3] < 0.024296675) {
                if (input[2] < 3.681081) {
                    var39 = 0.03147648;
                } else {
                    var39 = -0.042757522;
                }
            } else {
                if (input[8] < 9.0) {
                    var39 = -0.00021234836;
                } else {
                    var39 = -0.17932343;
                }
            }
        } else {
            if (input[4] < 0.011067524) {
                var39 = -0.1768271;
            } else {
                if (input[3] < 0.007047083) {
                    var39 = 0.023806706;
                } else {
                    var39 = -0.095155716;
                }
            }
        }
    } else {
        if (input[0] < 41.0) {
            if (input[0] < 27.0) {
                if (input[2] < 2.08) {
                    var39 = -0.03230723;
                } else {
                    var39 = 0.12413404;
                }
            } else {
                if (input[0] < 29.0) {
                    var39 = -0.24828605;
                } else {
                    var39 = 0.016193373;
                }
            }
        } else {
            if (input[8] < 26.0) {
                var39 = 0.17381841;
            } else {
                var39 = -0.01792521;
            }
        }
    }
    double var40;
    if (input[9] < 6.0) {
        if (input[1] < 19.0) {
            if (input[8] < 3.0) {
                if (input[2] < 2.08) {
                    var40 = 0.016761577;
                } else {
                    var40 = -0.07267747;
                }
            } else {
                if (input[9] < 3.0) {
                    var40 = -0.004877918;
                } else {
                    var40 = 0.18328702;
                }
            }
        } else {
            if (input[8] < 3.0) {
                if (input[2] < 2.0) {
                    var40 = -0.14675395;
                } else {
                    var40 = 0.182263;
                }
            } else {
                if (input[1] < 33.0) {
                    var40 = -0.0634447;
                } else {
                    var40 = 0.068808034;
                }
            }
        }
    } else {
        if (input[9] < 8.0) {
            if (input[0] < 590.0) {
                if (input[1] < 323.0) {
                    var40 = -0.027731547;
                } else {
                    var40 = -0.10178294;
                }
            } else {
                if (input[1] < 1995.0) {
                    var40 = 0.19234812;
                } else {
                    var40 = -0.029856283;
                }
            }
        } else {
            if (input[9] < 10.0) {
                if (input[4] < 0.0022490483) {
                    var40 = 0.19479164;
                } else {
                    var40 = 0.0026405721;
                }
            } else {
                if (input[4] < 0.003587338) {
                    var40 = -0.036190696;
                } else {
                    var40 = 0.1030127;
                }
            }
        }
    }
    double var41;
    if (input[3] < 0.0008933098) {
        if (input[4] < 0.002630761) {
            if (input[2] < 3.8358662) {
                if (input[3] < 0.00058559206) {
                    var41 = 0.10381234;
                } else {
                    var41 = -0.029361486;
                }
            } else {
                if (input[8] < 178.0) {
                    var41 = -0.007944438;
                } else {
                    var41 = -0.11321213;
                }
            }
        } else {
            if (input[8] < 119.0) {
                var41 = 0.24746564;
            } else {
                if (input[2] < 3.8358662) {
                    var41 = -0.04218167;
                } else {
                    var41 = 0.13481815;
                }
            }
        }
    } else {
        if (input[9] < 13.0) {
            if (input[2] < 3.7372549) {
                if (input[2] < 3.6880598) {
                    var41 = 0.0051310086;
                } else {
                    var41 = -0.119841;
                }
            } else {
                if (input[4] < 0.002554674) {
                    var41 = 0.25896102;
                } else {
                    var41 = -0.01943685;
                }
            }
        } else {
            if (input[9] < 31.0) {
                if (input[4] < 0.004369942) {
                    var41 = -0.13067381;
                } else {
                    var41 = 0.021807682;
                }
            } else {
                if (input[4] < 0.0026074378) {
                    var41 = 0.064933956;
                } else {
                    var41 = -0.09785588;
                }
            }
        }
    }
    double var42;
    if (input[3] < 0.0032132731) {
        if (input[1] < 1995.0) {
            if (input[9] < 12.0) {
                if (input[1] < 1082.0) {
                    var42 = 0.108117394;
                } else {
                    var42 = 0.22945501;
                }
            } else {
                if (input[9] < 15.0) {
                    var42 = -0.10103875;
                } else {
                    var42 = 0.1084412;
                }
            }
        } else {
            if (input[0] < 1507.0) {
                if (input[2] < 3.6581986) {
                    var42 = 0.0055439477;
                } else {
                    var42 = -0.110448584;
                }
            } else {
                if (input[9] < 16.0) {
                    var42 = 0.13117132;
                } else {
                    var42 = -0.0004895545;
                }
            }
        }
    } else {
        if (input[3] < 0.0039862623) {
            if (input[2] < 3.244392) {
                var42 = -0.010555803;
            } else {
                var42 = -0.15642786;
            }
        } else {
            if (input[1] < 603.0) {
                if (input[0] < 230.0) {
                    var42 = 0.0013073056;
                } else {
                    var42 = -0.096343525;
                }
            } else {
                if (input[2] < 3.6661632) {
                    var42 = 0.25748375;
                } else {
                    var42 = 0.1058066;
                }
            }
        }
    }
    double var43;
    if (input[4] < 0.04090909) {
        if (input[4] < 0.034848485) {
            if (input[4] < 0.02) {
                if (input[4] < 0.0062896824) {
                    var43 = 0.0031143012;
                } else {
                    var43 = -0.04358654;
                }
            } else {
                var43 = 0.118646376;
            }
        } else {
            var43 = -0.1345852;
        }
    } else {
        var43 = 0.13858008;
    }
    double var44;
    if (input[9] < 12.0) {
        if (input[9] < 8.0) {
            if (input[9] < 7.0) {
                if (input[3] < 0.075) {
                    var44 = 0.03177413;
                } else {
                    var44 = -0.008232479;
                }
            } else {
                if (input[2] < 2.7555556) {
                    var44 = -0.12617278;
                } else {
                    var44 = -0.0053506168;
                }
            }
        } else {
            if (input[8] < 20.0) {
                if (input[1] < 85.0) {
                    var44 = 0.15629916;
                } else {
                    var44 = -0.08079051;
                }
            } else {
                if (input[2] < 3.6115658) {
                    var44 = 0.1779968;
                } else {
                    var44 = -0.03760917;
                }
            }
        }
    } else {
        if (input[3] < 0.0012313456) {
            if (input[9] < 14.0) {
                var44 = 0.1886651;
            } else {
                if (input[8] < 83.0) {
                    var44 = 0.06671456;
                } else {
                    var44 = -0.033187352;
                }
            }
        } else {
            if (input[4] < 0.008151529) {
                if (input[8] < 21.0) {
                    var44 = 0.011580543;
                } else {
                    var44 = -0.12870531;
                }
            } else {
                var44 = 0.038978603;
            }
        }
    }
    double var45;
    if (input[4] < 0.04090909) {
        if (input[9] < 13.0) {
            if (input[3] < 0.024296675) {
                if (input[9] < 6.0) {
                    var45 = 0.09720738;
                } else {
                    var45 = 0.0075380253;
                }
            } else {
                if (input[8] < 10.0) {
                    var45 = -0.00023119897;
                } else {
                    var45 = -0.18571828;
                }
            }
        } else {
            if (input[8] < 61.0) {
                if (input[8] < 22.0) {
                    var45 = 0.040684342;
                } else {
                    var45 = -0.114931;
                }
            } else {
                if (input[8] < 78.0) {
                    var45 = 0.078003794;
                } else {
                    var45 = -0.029124249;
                }
            }
        }
    } else {
        var45 = 0.13454026;
    }
    double var46;
    if (input[4] < 0.04090909) {
        if (input[1] < 603.0) {
            if (input[8] < 26.0) {
                if (input[8] < 19.0) {
                    var46 = -0.0024426712;
                } else {
                    var46 = 0.099814236;
                }
            } else {
                if (input[3] < 0.0076621473) {
                    var46 = -0.15295519;
                } else {
                    var46 = 0.00035029952;
                }
            }
        } else {
            if (input[1] < 850.0) {
                if (input[4] < 0.005906787) {
                    var46 = 0.22676153;
                } else {
                    var46 = -0.0946337;
                }
            } else {
                if (input[2] < 3.4918478) {
                    var46 = 0.19075637;
                } else {
                    var46 = -0.016745081;
                }
            }
        }
    } else {
        var46 = 0.12969717;
    }
    double var47;
    if (input[3] < 0.0010299477) {
        if (input[8] < 78.0) {
            if (input[1] < 3.0) {
                var47 = 0.055680547;
            } else {
                var47 = 0.22188975;
            }
        } else {
            if (input[3] < 0.0008933098) {
                if (input[4] < 0.0014034595) {
                    var47 = -0.035432577;
                } else {
                    var47 = 0.13711415;
                }
            } else {
                if (input[2] < 3.5663116) {
                    var47 = 0.12956221;
                } else {
                    var47 = -0.10888936;
                }
            }
        }
    } else {
        if (input[3] < 0.079166666) {
            if (input[3] < 0.07619048) {
                if (input[2] < 2.0) {
                    var47 = -0.15086438;
                } else {
                    var47 = 0.0014823881;
                }
            } else {
                if (input[1] < 15.0) {
                    var47 = 0.15521619;
                } else {
                    var47 = -0.1531934;
                }
            }
        } else {
            if (input[6] < 13.0) {
                if (input[3] < 0.10909091) {
                    var47 = -0.09569313;
                } else {
                    var47 = 0.01990426;
                }
            } else {
                if (input[1] < 21.0) {
                    var47 = 0.13157216;
                } else {
                    var47 = -0.19046533;
                }
            }
        }
    }
    double var48;
    if (input[3] < 0.16666667) {
        if (input[2] < 2.142857) {
            if (input[2] < 2.1176472) {
                if (input[2] < 2.0) {
                    var48 = -0.08402585;
                } else {
                    var48 = 0.054192416;
                }
            } else {
                if (input[4] < 0.0003362915) {
                    var48 = -0.12727842;
                } else {
                    var48 = 0.096810445;
                }
            }
        } else {
            if (input[2] < 2.16) {
                var48 = 0.16346508;
            } else {
                if (input[1] < 13.0) {
                    var48 = 0.12552;
                } else {
                    var48 = -0.0060680537;
                }
            }
        }
    } else {
        if (input[0] < 6.0) {
            if (input[0] < 5.0) {
                var48 = 0.00192116;
            } else {
                var48 = 0.031102065;
            }
        } else {
            var48 = 0.08943768;
        }
    }
    double var49;
    if (input[2] < 3.7372549) {
        if (input[2] < 3.6880598) {
            if (input[3] < 0.0032132731) {
                if (input[1] < 2078.0) {
                    var49 = 0.11653143;
                } else {
                    var49 = -0.0015258663;
                }
            } else {
                if (input[1] < 363.0) {
                    var49 = 0.0030559509;
                } else {
                    var49 = -0.068052806;
                }
            }
        } else {
            if (input[1] < 866.0) {
                var49 = -0.016619122;
            } else {
                var49 = -0.13576226;
            }
        }
    } else {
        if (input[3] < 0.0012180067) {
            if (input[3] < 0.0008933098) {
                if (input[4] < 0.0013317748) {
                    var49 = -0.041324575;
                } else {
                    var49 = 0.1352473;
                }
            } else {
                if (input[4] < 0.002861309) {
                    var49 = -0.102332555;
                } else {
                    var49 = 0.00806484;
                }
            }
        } else {
            if (input[4] < 0.002554674) {
                if (input[3] < 0.005574695) {
                    var49 = 0.4425206;
                } else {
                    var49 = -0.007871976;
                }
            } else {
                if (input[2] < 3.7966588) {
                    var49 = -0.108164534;
                } else {
                    var49 = 0.09751177;
                }
            }
        }
    }
    double var50;
    if (input[4] < 0.04090909) {
        if (input[0] < 13.0) {
            if (input[1] < 13.0) {
                if (input[8] < 3.0) {
                    var50 = -0.0010964269;
                } else {
                    var50 = 0.13470301;
                }
            } else {
                if (input[9] < 4.0) {
                    var50 = -0.12065744;
                } else {
                    var50 = 0.18973452;
                }
            }
        } else {
            if (input[1] < 16.0) {
                if (input[9] < 3.0) {
                    var50 = 0.052647337;
                } else {
                    var50 = 0.16892701;
                }
            } else {
                if (input[1] < 17.0) {
                    var50 = -0.06954661;
                } else {
                    var50 = 0.005241915;
                }
            }
        }
    } else {
        var50 = 0.1252368;
    }
    double var51;
    if (input[4] < 0.01144816) {
        if (input[4] < 0.010373885) {
            if (input[3] < 0.075) {
                if (input[9] < 4.0) {
                    var51 = 0.09346186;
                } else {
                    var51 = -0.0066845543;
                }
            } else {
                if (input[3] < 0.079166666) {
                    var51 = -0.11899571;
                } else {
                    var51 = 0.006874212;
                }
            }
        } else {
            if (input[4] < 0.011067524) {
                var51 = -0.17014481;
            } else {
                if (input[3] < 0.007047083) {
                    var51 = 0.06346811;
                } else {
                    var51 = -0.07168913;
                }
            }
        }
    } else {
        if (input[3] < 0.033868093) {
            if (input[3] < 0.0073158885) {
                var51 = 0.026295867;
            } else {
                var51 = 0.16168267;
            }
        } else {
            if (input[0] < 27.0) {
                if (input[2] < 2.08) {
                    var51 = -0.05005545;
                } else {
                    var51 = 0.12921785;
                }
            } else {
                if (input[0] < 29.0) {
                    var51 = -0.24693647;
                } else {
                    var51 = -0.01763321;
                }
            }
        }
    }
    double var52;
    if (input[4] < 0.0003362915) {
        if (input[9] < 11.0) {
            if (input[9] < 8.0) {
                if (input[2] < 2.4705882) {
                    var52 = 0.0050775246;
                } else {
                    var52 = -0.043430157;
                }
            } else {
                if (input[3] < 0.023378141) {
                    var52 = 0.1951294;
                } else {
                    var52 = -0.033361267;
                }
            }
        } else {
            if (input[0] < 51.0) {
                var52 = 0.29325232;
            } else {
                if (input[0] < 172.0) {
                    var52 = -0.16246681;
                } else {
                    var52 = -0.0017810905;
                }
            }
        }
    } else {
        if (input[4] < 0.0026482379) {
            if (input[1] < 2078.0) {
                if (input[3] < 0.015644753) {
                    var52 = 0.12829694;
                } else {
                    var52 = -0.078374766;
                }
            } else {
                if (input[4] < 0.0023836766) {
                    var52 = -0.0037403675;
                } else {
                    var52 = 0.08782534;
                }
            }
        } else {
            if (input[3] < 0.0076621473) {
                if (input[4] < 0.0062896824) {
                    var52 = -0.006025337;
                } else {
                    var52 = -0.12586474;
                }
            } else {
                if (input[4] < 0.00472103) {
                    var52 = -0.053976953;
                } else {
                    var52 = 0.078365065;
                }
            }
        }
    }
    double var53;
    if (input[3] < 0.026008183) {
        if (input[8] < 6.0) {
            if (input[2] < 2.2222223) {
                var53 = -0.008660655;
            } else {
                if (input[3] < 0.020095188) {
                    var53 = 0.05855836;
                } else {
                    var53 = 0.24969;
                }
            }
        } else {
            if (input[3] < 0.02259887) {
                if (input[8] < 26.0) {
                    var53 = 0.04732905;
                } else {
                    var53 = -0.008767655;
                }
            } else {
                if (input[2] < 2.7) {
                    var53 = 0.06282291;
                } else {
                    var53 = -0.14440525;
                }
            }
        }
    } else {
        if (input[1] < 55.0) {
            if (input[2] < 2.7) {
                if (input[2] < 2.607143) {
                    var53 = -0.0013386566;
                } else {
                    var53 = -0.12112592;
                }
            } else {
                if (input[2] < 2.9473684) {
                    var53 = 0.5470669;
                } else {
                    var53 = -0.12471386;
                }
            }
        } else {
            if (input[8] < 7.0) {
                if (input[3] < 0.03503788) {
                    var53 = 0.09263924;
                } else {
                    var53 = -0.12605529;
                }
            } else {
                if (input[4] < 0.0050990204) {
                    var53 = -0.165155;
                } else {
                    var53 = -0.026791694;
                }
            }
        }
    }
    double var54;
    if (input[3] < 0.09848485) {
        if (input[1] < 16.0) {
            if (input[9] < 3.0) {
                if (input[3] < 0.08571429) {
                    var54 = 0.08969575;
                } else {
                    var54 = -0.061435893;
                }
            } else {
                if (input[2] < 2.16) {
                    var54 = 0.17737634;
                } else {
                    var54 = 0.033633634;
                }
            }
        } else {
            if (input[2] < 2.1666667) {
                if (input[1] < 20.0) {
                    var54 = -0.09295324;
                } else {
                    var54 = 0.058863766;
                }
            } else {
                if (input[2] < 2.4705882) {
                    var54 = 0.041242145;
                } else {
                    var54 = -0.0040468206;
                }
            }
        }
    } else {
        if (input[3] < 0.10909091) {
            if (input[9] < 4.0) {
                if (input[3] < 0.10606061) {
                    var54 = -0.06823643;
                } else {
                    var54 = -0.14957063;
                }
            } else {
                if (input[1] < 14.0) {
                    var54 = 0.20298505;
                } else {
                    var54 = 0.030475805;
                }
            }
        } else {
            if (input[3] < 0.11818182) {
                if (input[0] < 10.0) {
                    var54 = -0.006979679;
                } else {
                    var54 = 0.1442678;
                }
            } else {
                if (input[3] < 0.16666667) {
                    var54 = -0.0580715;
                } else {
                    var54 = 0.010030752;
                }
            }
        }
    }
    double var55;
    if (input[9] < 7.0) {
        if (input[0] < 21.0) {
            if (input[3] < 0.06666667) {
                if (input[8] < 4.0) {
                    var55 = -0.06413845;
                } else {
                    var55 = -0.27678975;
                }
            } else {
                if (input[3] < 0.075) {
                    var55 = 0.14561628;
                } else {
                    var55 = -0.009015853;
                }
            }
        } else {
            if (input[8] < 5.0) {
                if (input[4] < 0.015873017) {
                    var55 = 0.17768075;
                } else {
                    var55 = -0.10267114;
                }
            } else {
                if (input[3] < 0.025118984) {
                    var55 = 0.03770179;
                } else {
                    var55 = -0.15203393;
                }
            }
        }
    } else {
        if (input[2] < 2.7857144) {
            if (input[3] < 0.037195124) {
                if (input[0] < 80.0) {
                    var55 = 0.08938913;
                } else {
                    var55 = -0.11381454;
                }
            } else {
                if (input[9] < 9.0) {
                    var55 = -0.14578888;
                } else {
                    var55 = 0.048130095;
                }
            }
        } else {
            if (input[0] < 37.0) {
                if (input[2] < 2.9285715) {
                    var55 = 0.516499;
                } else {
                    var55 = -0.070126936;
                }
            } else {
                if (input[0] < 76.0) {
                    var55 = -0.1361249;
                } else {
                    var55 = 0.015216879;
                }
            }
        }
    }
    double var56;
    if (input[4] < 0.01172043) {
        if (input[4] < 0.010373885) {
            if (input[9] < 12.0) {
                if (input[9] < 8.0) {
                    var56 = -0.003885845;
                } else {
                    var56 = 0.035674457;
                }
            } else {
                if (input[3] < 0.0012313456) {
                    var56 = 0.010800521;
                } else {
                    var56 = -0.096413545;
                }
            }
        } else {
            if (input[4] < 0.011067524) {
                var56 = -0.16500896;
            } else {
                if (input[0] < 240.0) {
                    var56 = 0.004458936;
                } else {
                    var56 = -0.05703659;
                }
            }
        }
    } else {
        if (input[8] < 5.0) {
            if (input[3] < 0.06140351) {
                if (input[0] < 29.0) {
                    var56 = -0.14570355;
                } else {
                    var56 = 0.033913326;
                }
            } else {
                if (input[0] < 12.0) {
                    var56 = -0.039554365;
                } else {
                    var56 = 0.13713698;
                }
            }
        } else {
            var56 = 0.13958943;
        }
    }
    double var57;
    if (input[3] < 0.000867642) {
        if (input[2] < 3.9) {
            if (input[3] < 0.00058559206) {
                var57 = 0.124952346;
            } else {
                if (input[8] < 116.0) {
                    var57 = 0.1184083;
                } else {
                    var57 = -0.07697653;
                }
            }
        } else {
            if (input[2] < 3.956044) {
                if (input[1] < 8496.0) {
                    var57 = -0.0822739;
                } else {
                    var57 = -0.00874138;
                }
            } else {
                var57 = 0.09440728;
            }
        }
    } else {
        if (input[8] < 111.0) {
            if (input[2] < 3.780835) {
                if (input[2] < 3.681081) {
                    var57 = 0.0019059918;
                } else {
                    var57 = -0.06351613;
                }
            } else {
                if (input[3] < 0.005976994) {
                    var57 = 0.19981824;
                } else {
                    var57 = 0.02807329;
                }
            }
        } else {
            if (input[1] < 4005.0) {
                var57 = -0.116453975;
            } else {
                var57 = -0.0024415003;
            }
        }
    }
    double var58;
    if (input[1] < 603.0) {
        if (input[8] < 26.0) {
            if (input[4] < 0.0045634923) {
                if (input[8] < 9.0) {
                    var58 = -0.0019697275;
                } else {
                    var58 = -0.041123647;
                }
            } else {
                if (input[1] < 92.0) {
                    var58 = 0.006803072;
                } else {
                    var58 = 0.15285598;
                }
            }
        } else {
            if (input[3] < 0.0076621473) {
                if (input[8] < 32.0) {
                    var58 = -0.17458239;
                } else {
                    var58 = 0.11330325;
                }
            } else {
                if (input[1] < 245.0) {
                    var58 = -0.13919514;
                } else {
                    var58 = 0.10834276;
                }
            }
        }
    } else {
        if (input[1] < 850.0) {
            if (input[4] < 0.005906787) {
                if (input[8] < 28.0) {
                    var58 = 0.008635629;
                } else {
                    var58 = 0.24622968;
                }
            } else {
                var58 = -0.04920328;
            }
        } else {
            if (input[2] < 3.4918478) {
                var58 = 0.17324093;
            } else {
                if (input[1] < 1082.0) {
                    var58 = -0.15334158;
                } else {
                    var58 = 0.004453605;
                }
            }
        }
    }
    double var59;
    if (input[4] < 0.04090909) {
        if (input[4] < 0.034848485) {
            if (input[4] < 0.02) {
                if (input[4] < 0.015873017) {
                    var59 = 0.00066418527;
                } else {
                    var59 = -0.14475748;
                }
            } else {
                if (input[3] < 0.045584045) {
                    var59 = 0.03352395;
                } else {
                    var59 = 0.124425;
                }
            }
        } else {
            var59 = -0.1426993;
        }
    } else {
        var59 = 0.11345855;
    }
    double var60;
    if (input[2] < 3.7372549) {
        if (input[2] < 3.6963696) {
            if (input[4] < 0.0003362915) {
                if (input[9] < 11.0) {
                    var60 = 0.0011503462;
                } else {
                    var60 = -0.07926969;
                }
            } else {
                if (input[4] < 0.0026074378) {
                    var60 = 0.060601704;
                } else {
                    var60 = 0.00000409117;
                }
            }
        } else {
            var60 = -0.13593842;
        }
    } else {
        if (input[3] < 0.0012180067) {
            if (input[3] < 0.0008933098) {
                if (input[4] < 0.002630761) {
                    var60 = 0.008132296;
                } else {
                    var60 = 0.1263175;
                }
            } else {
                if (input[9] < 15.0) {
                    var60 = -0.031018628;
                } else {
                    var60 = -0.12507053;
                }
            }
        } else {
            if (input[4] < 0.002554674) {
                if (input[2] < 3.7846763) {
                    var60 = 0.3541263;
                } else {
                    var60 = 0.030630797;
                }
            } else {
                if (input[2] < 3.780835) {
                    var60 = -0.098667406;
                } else {
                    var60 = 0.050488204;
                }
            }
        }
    }
    double var61;
    if (input[4] < 0.04090909) {
        if (input[4] < 0.034848485) {
            if (input[4] < 0.02) {
                if (input[4] < 0.015873017) {
                    var61 = 0.0008640648;
                } else {
                    var61 = -0.12707464;
                }
            } else {
                if (input[3] < 0.045584045) {
                    var61 = 0.024483763;
                } else {
                    var61 = 0.11738077;
                }
            }
        } else {
            var61 = -0.12914725;
        }
    } else {
        var61 = 0.109381;
    }
    double var62;
    if (input[6] < 13.0) {
        if (input[1] < 13.0) {
            if (input[9] < 3.0) {
                if (input[3] < 0.16666667) {
                    var62 = -0.049153745;
                } else {
                    var62 = 0.017860506;
                }
            } else {
                if (input[4] < 0.0003362915) {
                    var62 = 0.15583731;
                } else {
                    var62 = -0.050633505;
                }
            }
        } else {
            if (input[8] < 3.0) {
                if (input[1] < 14.0) {
                    var62 = -0.076170675;
                } else {
                    var62 = -0.15613829;
                }
            } else {
                if (input[9] < 3.0) {
                    var62 = -0.034955677;
                } else {
                    var62 = 0.15813032;
                }
            }
        }
    } else {
        if (input[1] < 16.0) {
            if (input[9] < 3.0) {
                if (input[3] < 0.08571429) {
                    var62 = 0.12014673;
                } else {
                    var62 = -0.016469985;
                }
            } else {
                if (input[3] < 0.0952381) {
                    var62 = 0.16984667;
                } else {
                    var62 = 0.042573556;
                }
            }
        } else {
            if (input[1] < 17.0) {
                if (input[8] < 3.0) {
                    var62 = -0.09308109;
                } else {
                    var62 = 0.13310447;
                }
            } else {
                if (input[6] < 16.0) {
                    var62 = 0.16446058;
                } else {
                    var62 = 0.0029882013;
                }
            }
        }
    }
    double var63;
    if (input[8] < 64.0) {
        if (input[0] < 1287.0) {
            if (input[8] < 44.0) {
                if (input[9] < 12.0) {
                    var63 = 0.0021745302;
                } else {
                    var63 = -0.07874565;
                }
            } else {
                if (input[4] < 0.00268242) {
                    var63 = 0.15477389;
                } else {
                    var63 = -0.033495195;
                }
            }
        } else {
            if (input[3] < 0.001107093) {
                var63 = -0.041412156;
            } else {
                var63 = -0.13647361;
            }
        }
    } else {
        if (input[2] < 3.6614583) {
            if (input[8] < 78.0) {
                if (input[4] < 0.0029573939) {
                    var63 = 0.23765485;
                } else {
                    var63 = -0.015136012;
                }
            } else {
                if (input[2] < 3.5663116) {
                    var63 = 0.11223533;
                } else {
                    var63 = -0.06391697;
                }
            }
        } else {
            if (input[8] < 75.0) {
                var63 = -0.12243205;
            } else {
                if (input[9] < 16.0) {
                    var63 = 0.081988536;
                } else {
                    var63 = -0.020119684;
                }
            }
        }
    }
    double var64;
    if (input[9] < 7.0) {
        if (input[0] < 21.0) {
            if (input[0] < 17.0) {
                if (input[8] < 3.0) {
                    var64 = -0.011975863;
                } else {
                    var64 = 0.1410348;
                }
            } else {
                if (input[2] < 2.451613) {
                    var64 = -0.020883843;
                } else {
                    var64 = -0.22823408;
                }
            }
        } else {
            if (input[8] < 4.0) {
                if (input[4] < 0.018518519) {
                    var64 = 0.16838296;
                } else {
                    var64 = -0.0717829;
                }
            } else {
                if (input[1] < 36.0) {
                    var64 = -0.25630727;
                } else {
                    var64 = 0.018662406;
                }
            }
        }
    } else {
        if (input[1] < 39.0) {
            if (input[9] < 8.0) {
                var64 = -0.15010355;
            } else {
                var64 = 0.133013;
            }
        } else {
            if (input[1] < 85.0) {
                if (input[2] < 2.9473684) {
                    var64 = 0.15874518;
                } else {
                    var64 = -0.1042352;
                }
            } else {
                if (input[8] < 13.0) {
                    var64 = -0.11707979;
                } else {
                    var64 = 0.010046458;
                }
            }
        }
    }
    double var65;
    if (input[4] < 0.04090909) {
        if (input[4] < 0.034848485) {
            if (input[4] < 0.02) {
                if (input[1] < 19.0) {
                    var65 = -0.012745623;
                } else {
                    var65 = 0.004510698;
                }
            } else {
                if (input[3] < 0.045584045) {
                    var65 = 0.035034634;
                } else {
                    var65 = 0.11905379;
                }
            }
        } else {
            var65 = -0.11485836;
        }
    } else {
        var65 = 0.10661567;
    }
    double var66;
    if (input[4] < 0.0026482379) {
        if (input[4] < 0.0003362915) {
            if (input[9] < 11.0) {
                if (input[1] < 113.0) {
                    var66 = -0.0073451246;
                } else {
                    var66 = 0.08027574;
                }
            } else {
                if (input[0] < 51.0) {
                    var66 = 0.23329347;
                } else {
                    var66 = -0.12157344;
                }
            }
        } else {
            if (input[8] < 24.0) {
                if (input[4] < 0.0023836766) {
                    var66 = 0.15949781;
                } else {
                    var66 = 0.04267947;
                }
            } else {
                if (input[0] < 283.0) {
                    var66 = -0.08555516;
                } else {
                    var66 = 0.041594137;
                }
            }
        }
    } else {
        if (input[8] < 26.0) {
            if (input[0] < 94.0) {
                if (input[9] < 7.0) {
                    var66 = 0.047377836;
                } else {
                    var66 = -0.10842122;
                }
            } else {
                if (input[4] < 0.0033783785) {
                    var66 = -0.008491107;
                } else {
                    var66 = 0.1541692;
                }
            }
        } else {
            if (input[8] < 28.0) {
                if (input[0] < 246.0) {
                    var66 = 0.010183147;
                } else {
                    var66 = -0.1709493;
                }
            } else {
                if (input[8] < 30.0) {
                    var66 = 0.107744545;
                } else {
                    var66 = -0.06282798;
                }
            }
        }
    }
    double var67;
    if (input[3] < 0.00058559206) {
        if (input[4] < 0.0013043031) {
            if (input[4] < 0.0011527161) {
                var67 = 0.100808814;
            } else {
                var67 = -0.09028213;
            }
        } else {
            var67 = 0.148888;
        }
    } else {
        if (input[2] < 3.6795666) {
            if (input[2] < 3.6644194) {
                if (input[9] < 8.0) {
                    var67 = -0.008754462;
                } else {
                    var67 = 0.027911838;
                }
            } else {
                if (input[8] < 30.0) {
                    var67 = 0.22042176;
                } else {
                    var67 = -0.09259853;
                }
            }
        } else {
            if (input[2] < 3.7372549) {
                if (input[0] < 1598.0) {
                    var67 = -0.12355283;
                } else {
                    var67 = -0.022108952;
                }
            } else {
                if (input[3] < 0.0012180067) {
                    var67 = -0.04627893;
                } else {
                    var67 = 0.12303619;
                }
            }
        }
    }
    double var68;
    if (input[9] < 4.0) {
        if (input[6] < 19.0) {
            if (input[1] < 21.0) {
                if (input[2] < 2.375) {
                    var68 = -0.008028904;
                } else {
                    var68 = 0.18128061;
                }
            } else {
                if (input[2] < 2.3428571) {
                    var68 = 0.11957971;
                } else {
                    var68 = -0.21694054;
                }
            }
        } else {
            if (input[4] < 0.015873017) {
                if (input[3] < 0.044159543) {
                    var68 = 0.1316914;
                } else {
                    var68 = 0.073572084;
                }
            } else {
                if (input[4] < 0.020959595) {
                    var68 = -0.21869501;
                } else {
                    var68 = 0.09764738;
                }
            }
        }
    } else {
        if (input[1] < 14.0) {
            var68 = 0.18252973;
        } else {
            if (input[2] < 2.347826) {
                if (input[2] < 2.2962964) {
                    var68 = -0.004094947;
                } else {
                    var68 = -0.1834268;
                }
            } else {
                if (input[2] < 2.607143) {
                    var68 = 0.06291446;
                } else {
                    var68 = -0.010857591;
                }
            }
        }
    }
    double var69;
    if (input[3] < 0.079166666) {
        if (input[3] < 0.075) {
            if (input[3] < 0.068627454) {
                if (input[3] < 0.023378141) {
                    var69 = 0.0075014094;
                } else {
                    var69 = -0.027270647;
                }
            } else {
                if (input[2] < 2.3636363) {
                    var69 = 0.12924904;
                } else {
                    var69 = -0.053484626;
                }
            }
        } else {
            if (input[0] < 15.0) {
                var69 = 0.12626877;
            } else {
                if (input[4] < 0.0003362915) {
                    var69 = -0.09427325;
                } else {
                    var69 = 0.08876383;
                }
            }
        }
    } else {
        if (input[3] < 0.08571429) {
            if (input[9] < 4.0) {
                var69 = 0.18221529;
            } else {
                if (input[8] < 3.0) {
                    var69 = -0.09254901;
                } else {
                    var69 = 0.07926624;
                }
            }
        } else {
            if (input[2] < 2.3225806) {
                if (input[8] < 3.0) {
                    var69 = 0.000895866;
                } else {
                    var69 = 0.09893936;
                }
            } else {
                if (input[2] < 2.3428571) {
                    var69 = -0.14094263;
                } else {
                    var69 = 0.016325237;
                }
            }
        }
    }
    double var70;
    if (input[3] < 0.16666667) {
        if (input[0] < 13.0) {
            if (input[8] < 3.0) {
                if (input[1] < 13.0) {
                    var70 = -0.019305302;
                } else {
                    var70 = -0.112047695;
                }
            } else {
                if (input[9] < 3.0) {
                    var70 = -0.029218134;
                } else {
                    var70 = 0.15119733;
                }
            }
        } else {
            if (input[1] < 16.0) {
                if (input[9] < 3.0) {
                    var70 = 0.042975742;
                } else {
                    var70 = 0.1558375;
                }
            } else {
                if (input[1] < 17.0) {
                    var70 = -0.053463742;
                } else {
                    var70 = 0.0024465388;
                }
            }
        }
    } else {
        if (input[0] < 6.0) {
            if (input[0] < 5.0) {
                var70 = 0.003577121;
            } else {
                var70 = 0.02736571;
            }
        } else {
            if (input[0] < 7.0) {
                var70 = 0.108023375;
            } else {
                var70 = 0.052547548;
            }
        }
    }
    double var71;
    if (input[8] < 9.0) {
        if (input[0] < 49.0) {
            if (input[9] < 11.0) {
                if (input[9] < 7.0) {
                    var71 = 0.008430018;
                } else {
                    var71 = -0.06296636;
                }
            } else {
                var71 = 0.20772666;
            }
        } else {
            if (input[2] < 2.7) {
                if (input[9] < 11.0) {
                    var71 = 0.17590357;
                } else {
                    var71 = -0.025736779;
                }
            } else {
                if (input[8] < 7.0) {
                    var71 = 0.1846582;
                } else {
                    var71 = -0.11742479;
                }
            }
        }
    } else {
        if (input[1] < 113.0) {
            if (input[4] < 0.0050990204) {
                if (input[2] < 2.6666667) {
                    var71 = -0.0061657093;
                } else {
                    var71 = -0.15202306;
                }
            } else {
                var71 = 0.05092966;
            }
        } else {
            if (input[2] < 2.6666667) {
                if (input[9] < 4.0) {
                    var71 = -0.019866733;
                } else {
                    var71 = -0.15068;
                }
            } else {
                if (input[1] < 323.0) {
                    var71 = 0.07599672;
                } else {
                    var71 = -0.008883041;
                }
            }
        }
    }
    double var72;
    if (input[9] < 14.0) {
        if (input[8] < 66.0) {
            if (input[0] < 1287.0) {
                if (input[9] < 8.0) {
                    var72 = -0.0037958303;
                } else {
                    var72 = 0.040908918;
                }
            } else {
                var72 = -0.14142902;
            }
        } else {
            if (input[2] < 3.7506702) {
                if (input[1] < 3316.0) {
                    var72 = 0.24583733;
                } else {
                    var72 = 0.0012483128;
                }
            } else {
                if (input[8] < 99.0) {
                    var72 = -0.10610416;
                } else {
                    var72 = 0.04964638;
                }
            }
        }
    } else {
        if (input[4] < 0.0021320346) {
            if (input[0] < 172.0) {
                var72 = -0.12711592;
            } else {
                if (input[4] < 0.0012893142) {
                    var72 = 0.038938735;
                } else {
                    var72 = -0.10705778;
                }
            }
        } else {
            if (input[3] < 0.000867642) {
                var72 = 0.11257288;
            } else {
                if (input[4] < 0.0026074378) {
                    var72 = 0.036561467;
                } else {
                    var72 = -0.076234095;
                }
            }
        }
    }
    double var73;
    if (input[4] < 0.011067524) {
        if (input[4] < 0.010373885) {
            if (input[8] < 8.0) {
                if (input[1] < 39.0) {
                    var73 = -0.0037919753;
                } else {
                    var73 = 0.074097976;
                }
            } else {
                if (input[3] < 0.022213995) {
                    var73 = 0.0019246936;
                } else {
                    var73 = -0.12822838;
                }
            }
        } else {
            var73 = -0.15699083;
        }
    } else {
        if (input[9] < 8.0) {
            if (input[8] < 4.0) {
                if (input[1] < 12.0) {
                    var73 = -0.043766957;
                } else {
                    var73 = 0.099450774;
                }
            } else {
                if (input[2] < 2.5333333) {
                    var73 = -0.2895865;
                } else {
                    var73 = 0.060706243;
                }
            }
        } else {
            var73 = 0.14577141;
        }
    }
    double var74;
    if (input[2] < 3.7372549) {
        if (input[2] < 3.6963696) {
            if (input[9] < 13.0) {
                if (input[8] < 66.0) {
                    var74 = -0.00043570815;
                } else {
                    var74 = 0.13472037;
                }
            } else {
                if (input[8] < 83.0) {
                    var74 = -0.017020034;
                } else {
                    var74 = -0.14484206;
                }
            }
        } else {
            var74 = -0.12661146;
        }
    } else {
        if (input[2] < 3.7506702) {
            if (input[4] < 0.002554674) {
                var74 = 0.25881028;
            } else {
                var74 = -0.018628031;
            }
        } else {
            if (input[9] < 8.0) {
                var74 = 0.122918844;
            } else {
                if (input[2] < 3.780835) {
                    var74 = -0.08979398;
                } else {
                    var74 = 0.030300006;
                }
            }
        }
    }
    double var75;
    if (input[9] < 7.0) {
        if (input[8] < 33.0) {
            if (input[1] < 323.0) {
                if (input[0] < 65.0) {
                    var75 = 0.0033431454;
                } else {
                    var75 = 0.12786986;
                }
            } else {
                if (input[2] < 3.6644194) {
                    var75 = -0.103305385;
                } else {
                    var75 = 0.054583818;
                }
            }
        } else {
            var75 = 0.13208427;
        }
    } else {
        if (input[2] < 2.7555556) {
            if (input[2] < 2.607143) {
                if (input[8] < 9.0) {
                    var75 = 0.0034928068;
                } else {
                    var75 = -0.1433044;
                }
            } else {
                if (input[8] < 15.0) {
                    var75 = -0.14119436;
                } else {
                    var75 = 0.10165299;
                }
            }
        } else {
            if (input[1] < 49.0) {
                if (input[0] < 31.0) {
                    var75 = 0.13351433;
                } else {
                    var75 = 0.40219396;
                }
            } else {
                if (input[8] < 12.0) {
                    var75 = -0.108650126;
                } else {
                    var75 = 0.010278635;
                }
            }
        }
    }
    double var76;
    if (input[8] < 8.0) {
        if (input[6] < 33.0) {
            if (input[9] < 7.0) {
                if (input[8] < 4.0) {
                    var76 = 0.011957504;
                } else {
                    var76 = -0.1022045;
                }
            } else {
                if (input[2] < 2.7) {
                    var76 = -0.11796709;
                } else {
                    var76 = 0.10731602;
                }
            }
        } else {
            if (input[2] < 2.9655173) {
                if (input[2] < 2.7857144) {
                    var76 = 0.041457586;
                } else {
                    var76 = 0.296428;
                }
            } else {
                if (input[2] < 2.9909909) {
                    var76 = -0.112996824;
                } else {
                    var76 = -0.020163527;
                }
            }
        }
    } else {
        if (input[3] < 0.022213995) {
            if (input[2] < 2.5333333) {
                if (input[8] < 9.0) {
                    var76 = -0.032301124;
                } else {
                    var76 = -0.19199617;
                }
            } else {
                if (input[1] < 323.0) {
                    var76 = 0.05096091;
                } else {
                    var76 = -0.011532055;
                }
            }
        } else {
            if (input[6] < 31.0) {
                var76 = 0.09434625;
            } else {
                if (input[2] < 3.1601562) {
                    var76 = -0.14040108;
                } else {
                    var76 = -0.05323595;
                }
            }
        }
    }
    double var77;
    if (input[9] < 14.0) {
        if (input[8] < 66.0) {
            if (input[0] < 1287.0) {
                if (input[2] < 3.6644194) {
                    var77 = 0.00035304486;
                } else {
                    var77 = 0.078984566;
                }
            } else {
                var77 = -0.13764729;
            }
        } else {
            if (input[4] < 0.0019419115) {
                var77 = 0.19371882;
            } else {
                if (input[4] < 0.0028409092) {
                    var77 = -0.05311055;
                } else {
                    var77 = 0.12382205;
                }
            }
        }
    } else {
        if (input[4] < 0.004369942) {
            if (input[0] < 172.0) {
                var77 = -0.13687551;
            } else {
                if (input[4] < 0.003061078) {
                    var77 = 0.0015247469;
                } else {
                    var77 = -0.14092676;
                }
            }
        } else {
            if (input[1] < 548.0) {
                var77 = 0.11924968;
            } else {
                var77 = 0.024638498;
            }
        }
    }
    double var78;
    if (input[4] < 0.04090909) {
        if (input[4] < 0.034848485) {
            if (input[4] < 0.02) {
                if (input[4] < 0.007936508) {
                    var78 = 0.00036871832;
                } else {
                    var78 = -0.033601638;
                }
            } else {
                if (input[3] < 0.045584045) {
                    var78 = 0.01746887;
                } else {
                    var78 = 0.106664196;
                }
            }
        } else {
            var78 = -0.11243538;
        }
    } else {
        var78 = 0.09810692;
    }
    double var79;
    if (input[2] < 2.1176472) {
        if (input[2] < 2.0) {
            if (input[9] < 5.0) {
                if (input[0] < 10.0) {
                    var79 = -0.0029444685;
                } else {
                    var79 = 0.08320886;
                }
            } else {
                var79 = -0.11506715;
            }
        } else {
            if (input[0] < 13.0) {
                if (input[0] < 8.0) {
                    var79 = 0.04706566;
                } else {
                    var79 = -0.0041599358;
                }
            } else {
                if (input[9] < 6.0) {
                    var79 = 0.18483426;
                } else {
                    var79 = -0.061940055;
                }
            }
        }
    } else {
        if (input[2] < 2.142857) {
            if (input[8] < 3.0) {
                if (input[0] < 17.0) {
                    var79 = -0.07456143;
                } else {
                    var79 = -0.14767489;
                }
            } else {
                var79 = 0.20173311;
            }
        } else {
            if (input[2] < 2.16) {
                var79 = 0.11253748;
            } else {
                if (input[1] < 15.0) {
                    var79 = -0.0467259;
                } else {
                    var79 = 0.003942735;
                }
            }
        }
    }
    double var80;
    if (input[9] < 8.0) {
        if (input[3] < 0.008626676) {
            if (input[2] < 3.6434782) {
                if (input[8] < 36.0) {
                    var80 = -0.10236;
                } else {
                    var80 = 0.10464628;
                }
            } else {
                if (input[3] < 0.0039862623) {
                    var80 = -0.0207868;
                } else {
                    var80 = 0.106358;
                }
            }
        } else {
            if (input[8] < 16.0) {
                if (input[9] < 7.0) {
                    var80 = 0.0057003647;
                } else {
                    var80 = -0.04693438;
                }
            } else {
                if (input[2] < 3.0769231) {
                    var80 = 0.056403592;
                } else {
                    var80 = 0.17194058;
                }
            }
        }
    } else {
        if (input[9] < 9.0) {
            if (input[2] < 2.9655173) {
                var80 = 0.18950118;
            } else {
                if (input[8] < 28.0) {
                    var80 = -0.07903178;
                } else {
                    var80 = 0.09897697;
                }
            }
        } else {
            if (input[2] < 2.868421) {
                if (input[8] < 6.0) {
                    var80 = 0.04280985;
                } else {
                    var80 = -0.13195156;
                }
            } else {
                if (input[8] < 17.0) {
                    var80 = 0.19343874;
                } else {
                    var80 = 0.0043077003;
                }
            }
        }
    }
    double var81;
    if (input[4] < 0.04090909) {
        if (input[4] < 0.034848485) {
            if (input[4] < 0.02) {
                if (input[4] < 0.015873017) {
                    var81 = 0.0008656913;
                } else {
                    var81 = -0.12103527;
                }
            } else {
                if (input[3] < 0.045584045) {
                    var81 = 0.0121051995;
                } else {
                    var81 = 0.10137594;
                }
            }
        } else {
            var81 = -0.10296679;
        }
    } else {
        var81 = 0.09419636;
    }
    double var82;
    if (input[2] < 2.090909) {
        if (input[2] < 2.0) {
            if (input[9] < 5.0) {
                if (input[0] < 9.0) {
                    var82 = 0.008856972;
                } else {
                    var82 = 0.07955053;
                }
            } else {
                var82 = -0.11625267;
            }
        } else {
            if (input[0] < 13.0) {
                if (input[0] < 8.0) {
                    var82 = 0.060116954;
                } else {
                    var82 = 0.009348706;
                }
            } else {
                if (input[9] < 6.0) {
                    var82 = 0.19030495;
                } else {
                    var82 = 0.0042564585;
                }
            }
        }
    } else {
        if (input[2] < 2.142857) {
            if (input[8] < 3.0) {
                if (input[0] < 18.0) {
                    var82 = -0.09094508;
                } else {
                    var82 = 0.012215611;
                }
            } else {
                var82 = 0.13886465;
            }
        } else {
            if (input[2] < 2.16) {
                var82 = 0.10887565;
            } else {
                if (input[1] < 13.0) {
                    var82 = 0.10305123;
                } else {
                    var82 = -0.0034158095;
                }
            }
        }
    }
    double var83;
    if (input[9] < 12.0) {
        if (input[2] < 3.7372549) {
            if (input[2] < 3.681081) {
                if (input[2] < 3.6782477) {
                    var83 = 0.004741894;
                } else {
                    var83 = 0.13343237;
                }
            } else {
                if (input[1] < 866.0) {
                    var83 = -0.03872634;
                } else {
                    var83 = -0.11322225;
                }
            }
        } else {
            if (input[0] < 1524.0) {
                if (input[9] < 11.0) {
                    var83 = 0.054329373;
                } else {
                    var83 = 0.17928737;
                }
            } else {
                var83 = -0.024958955;
            }
        }
    } else {
        if (input[8] < 61.0) {
            if (input[8] < 22.0) {
                if (input[1] < 131.0) {
                    var83 = -0.040917866;
                } else {
                    var83 = 0.11482804;
                }
            } else {
                if (input[8] < 37.0) {
                    var83 = -0.13436608;
                } else {
                    var83 = -0.054697;
                }
            }
        } else {
            if (input[8] < 65.0) {
                var83 = 0.13686056;
            } else {
                if (input[0] < 1761.0) {
                    var83 = -0.052252006;
                } else {
                    var83 = 0.025907936;
                }
            }
        }
    }
    double var84;
    if (input[2] < 2.3428571) {
        if (input[2] < 2.2857144) {
            if (input[6] < 21.0) {
                if (input[3] < 0.06666667) {
                    var84 = -0.07654229;
                } else {
                    var84 = 0.0058617187;
                }
            } else {
                if (input[9] < 7.0) {
                    var84 = 0.12876809;
                } else {
                    var84 = -0.07458284;
                }
            }
        } else {
            if (input[9] < 5.0) {
                if (input[9] < 4.0) {
                    var84 = -0.027250176;
                } else {
                    var84 = -0.3359716;
                }
            } else {
                if (input[2] < 2.3333333) {
                    var84 = -0.031358235;
                } else {
                    var84 = 0.21204521;
                }
            }
        }
    } else {
        if (input[1] < 21.0) {
            if (input[1] < 14.0) {
                var84 = 0.0066040726;
            } else {
                if (input[9] < 5.0) {
                    var84 = 0.17451066;
                } else {
                    var84 = 0.022518732;
                }
            }
        } else {
            if (input[3] < 0.068627454) {
                if (input[6] < 37.0) {
                    var84 = 0.0522463;
                } else {
                    var84 = -0.0012283189;
                }
            } else {
                if (input[9] < 4.0) {
                    var84 = -0.19890633;
                } else {
                    var84 = 0.017469073;
                }
            }
        }
    }
    double var85;
    if (input[8] < 60.0) {
        if (input[0] < 1203.0) {
            if (input[8] < 42.0) {
                if (input[8] < 26.0) {
                    var85 = 0.0018016375;
                } else {
                    var85 = -0.034342095;
                }
            } else {
                if (input[2] < 3.5663116) {
                    var85 = 0.18036549;
                } else {
                    var85 = -0.049886607;
                }
            }
        } else {
            if (input[4] < 0.0009916509) {
                if (input[2] < 3.6480837) {
                    var85 = 0.06535387;
                } else {
                    var85 = -0.00432259;
                }
            } else {
                var85 = -0.12713526;
            }
        }
    } else {
        if (input[8] < 83.0) {
            if (input[4] < 0.0026074378) {
                if (input[4] < 0.0011843292) {
                    var85 = -0.06002548;
                } else {
                    var85 = 0.1888461;
                }
            } else {
                if (input[2] < 3.6480837) {
                    var85 = 0.056750923;
                } else {
                    var85 = -0.12013887;
                }
            }
        } else {
            if (input[2] < 3.7372549) {
                if (input[9] < 13.0) {
                    var85 = 0.008963407;
                } else {
                    var85 = -0.14245135;
                }
            } else {
                if (input[4] < 0.0021984552) {
                    var85 = -0.03516386;
                } else {
                    var85 = 0.03872406;
                }
            }
        }
    }
    double var86;
    var86 = sigmoid(var0 + var1 + var2 + var3 + var4 + var5 + var6 + var7 + var8 + var9 + var10 + var11 + var12 + var13 + var14 + var15 + var16 + var17 + var18 + var19 + var20 + var21 + var22 + var23 + var24 + var25 + var26 + var27 + var28 + var29 + var30 + var31 + var32 + var33 + var34 + var35 + var36 + var37 + var38 + var39 + var40 + var41 + var42 + var43 + var44 + var45 + var46 + var47 + var48 + var49 + var50 + var51 + var52 + var53 + var54 + var55 + var56 + var57 + var58 + var59 + var60 + var61 + var62 + var63 + var64 + var65 + var66 + var67 + var68 + var69 + var70 + var71 + var72 + var73 + var74 + var75 + var76 + var77 + var78 + var79 + var80 + var81 + var82 + var83 + var84 + var85);
    memcpy(output, (double[]){1.0 - var86, var86}, 2 * sizeof(double));
}

