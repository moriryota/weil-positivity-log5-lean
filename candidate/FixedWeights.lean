import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Tactic
namespace RHFixedWeights
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
lemma h0 : harmonic 0 = 0 := harmonic_zero
lemma h1 : harmonic 1 = (1 : ℚ) / 1 := by
  rw [show 1 = 0+1 from rfl, harmonic_succ, h0]
  norm_num
lemma h2 : harmonic 2 = (3 : ℚ) / 2 := by
  rw [show 2 = 1+1 from rfl, harmonic_succ, h1]
  norm_num
lemma h3 : harmonic 3 = (11 : ℚ) / 6 := by
  rw [show 3 = 2+1 from rfl, harmonic_succ, h2]
  norm_num
lemma h4 : harmonic 4 = (25 : ℚ) / 12 := by
  rw [show 4 = 3+1 from rfl, harmonic_succ, h3]
  norm_num
lemma h5 : harmonic 5 = (137 : ℚ) / 60 := by
  rw [show 5 = 4+1 from rfl, harmonic_succ, h4]
  norm_num
lemma h6 : harmonic 6 = (49 : ℚ) / 20 := by
  rw [show 6 = 5+1 from rfl, harmonic_succ, h5]
  norm_num
lemma h7 : harmonic 7 = (363 : ℚ) / 140 := by
  rw [show 7 = 6+1 from rfl, harmonic_succ, h6]
  norm_num
lemma h8 : harmonic 8 = (761 : ℚ) / 280 := by
  rw [show 8 = 7+1 from rfl, harmonic_succ, h7]
  norm_num
lemma h9 : harmonic 9 = (7129 : ℚ) / 2520 := by
  rw [show 9 = 8+1 from rfl, harmonic_succ, h8]
  norm_num
lemma h10 : harmonic 10 = (7381 : ℚ) / 2520 := by
  rw [show 10 = 9+1 from rfl, harmonic_succ, h9]
  norm_num
lemma h11 : harmonic 11 = (83711 : ℚ) / 27720 := by
  rw [show 11 = 10+1 from rfl, harmonic_succ, h10]
  norm_num
lemma h12 : harmonic 12 = (86021 : ℚ) / 27720 := by
  rw [show 12 = 11+1 from rfl, harmonic_succ, h11]
  norm_num
lemma h13 : harmonic 13 = (1145993 : ℚ) / 360360 := by
  rw [show 13 = 12+1 from rfl, harmonic_succ, h12]
  norm_num
lemma h14 : harmonic 14 = (1171733 : ℚ) / 360360 := by
  rw [show 14 = 13+1 from rfl, harmonic_succ, h13]
  norm_num
lemma h15 : harmonic 15 = (1195757 : ℚ) / 360360 := by
  rw [show 15 = 14+1 from rfl, harmonic_succ, h14]
  norm_num
lemma h16 : harmonic 16 = (2436559 : ℚ) / 720720 := by
  rw [show 16 = 15+1 from rfl, harmonic_succ, h15]
  norm_num
lemma h17 : harmonic 17 = (42142223 : ℚ) / 12252240 := by
  rw [show 17 = 16+1 from rfl, harmonic_succ, h16]
  norm_num
lemma h18 : harmonic 18 = (14274301 : ℚ) / 4084080 := by
  rw [show 18 = 17+1 from rfl, harmonic_succ, h17]
  norm_num
lemma h19 : harmonic 19 = (275295799 : ℚ) / 77597520 := by
  rw [show 19 = 18+1 from rfl, harmonic_succ, h18]
  norm_num
lemma h20 : harmonic 20 = (55835135 : ℚ) / 15519504 := by
  rw [show 20 = 19+1 from rfl, harmonic_succ, h19]
  norm_num
lemma h21 : harmonic 21 = (18858053 : ℚ) / 5173168 := by
  rw [show 21 = 20+1 from rfl, harmonic_succ, h20]
  norm_num
lemma h22 : harmonic 22 = (19093197 : ℚ) / 5173168 := by
  rw [show 22 = 21+1 from rfl, harmonic_succ, h21]
  norm_num
lemma h23 : harmonic 23 = (444316699 : ℚ) / 118982864 := by
  rw [show 23 = 22+1 from rfl, harmonic_succ, h22]
  norm_num
lemma h24 : harmonic 24 = (1347822955 : ℚ) / 356948592 := by
  rw [show 24 = 23+1 from rfl, harmonic_succ, h23]
  norm_num
lemma h25 : harmonic 25 = (34052522467 : ℚ) / 8923714800 := by
  rw [show 25 = 24+1 from rfl, harmonic_succ, h24]
  norm_num
lemma h26 : harmonic 26 = (34395742267 : ℚ) / 8923714800 := by
  rw [show 26 = 25+1 from rfl, harmonic_succ, h25]
  norm_num
lemma h27 : harmonic 27 = (312536252003 : ℚ) / 80313433200 := by
  rw [show 27 = 26+1 from rfl, harmonic_succ, h26]
  norm_num
lemma h28 : harmonic 28 = (315404588903 : ℚ) / 80313433200 := by
  rw [show 28 = 27+1 from rfl, harmonic_succ, h27]
  norm_num
lemma h29 : harmonic 29 = (9227046511387 : ℚ) / 2329089562800 := by
  rw [show 29 = 28+1 from rfl, harmonic_succ, h28]
  norm_num
lemma h30 : harmonic 30 = (9304682830147 : ℚ) / 2329089562800 := by
  rw [show 30 = 29+1 from rfl, harmonic_succ, h29]
  norm_num
lemma h31 : harmonic 31 = (290774257297357 : ℚ) / 72201776446800 := by
  rw [show 31 = 30+1 from rfl, harmonic_succ, h30]
  norm_num
lemma h32 : harmonic 32 = (586061125622639 : ℚ) / 144403552893600 := by
  rw [show 32 = 31+1 from rfl, harmonic_succ, h31]
  norm_num
lemma h33 : harmonic 33 = (53676090078349 : ℚ) / 13127595717600 := by
  rw [show 33 = 32+1 from rfl, harmonic_succ, h32]
  norm_num
lemma h34 : harmonic 34 = (54062195834749 : ℚ) / 13127595717600 := by
  rw [show 34 = 33+1 from rfl, harmonic_succ, h33]
  norm_num
lemma h35 : harmonic 35 = (54437269998109 : ℚ) / 13127595717600 := by
  rw [show 35 = 34+1 from rfl, harmonic_succ, h34]
  norm_num
lemma h36 : harmonic 36 = (54801925434709 : ℚ) / 13127595717600 := by
  rw [show 36 = 35+1 from rfl, harmonic_succ, h35]
  norm_num
lemma h37 : harmonic 37 = (2040798836801833 : ℚ) / 485721041551200 := by
  rw [show 37 = 36+1 from rfl, harmonic_succ, h36]
  norm_num
lemma h38 : harmonic 38 = (2053580969474233 : ℚ) / 485721041551200 := by
  rw [show 38 = 37+1 from rfl, harmonic_succ, h37]
  norm_num
lemma h39 : harmonic 39 = (2066035355155033 : ℚ) / 485721041551200 := by
  rw [show 39 = 38+1 from rfl, harmonic_succ, h38]
  norm_num
lemma h40 : harmonic 40 = (2078178381193813 : ℚ) / 485721041551200 := by
  rw [show 40 = 39+1 from rfl, harmonic_succ, h39]
  norm_num
lemma h41 : harmonic 41 = (85691034670497533 : ℚ) / 19914562703599200 := by
  rw [show 41 = 40+1 from rfl, harmonic_succ, h40]
  norm_num
lemma h42 : harmonic 42 = (12309312989335019 : ℚ) / 2844937529085600 := by
  rw [show 42 = 41+1 from rfl, harmonic_succ, h41]
  norm_num
lemma h43 : harmonic 43 = (532145396070491417 : ℚ) / 122332313750680800 := by
  rw [show 43 = 42+1 from rfl, harmonic_succ, h42]
  norm_num
lemma h44 : harmonic 44 = (5884182435213075787 : ℚ) / 1345655451257488800 := by
  rw [show 44 = 43+1 from rfl, harmonic_succ, h43]
  norm_num
lemma h45 : harmonic 45 = (5914085889685464427 : ℚ) / 1345655451257488800 := by
  rw [show 45 = 44+1 from rfl, harmonic_succ, h44]
  norm_num
lemma h46 : harmonic 46 = (5943339269060627227 : ℚ) / 1345655451257488800 := by
  rw [show 46 = 45+1 from rfl, harmonic_succ, h45]
  norm_num
lemma h47 : harmonic 47 = (280682601097106968469 : ℚ) / 63245806209101973600 := by
  rw [show 47 = 46+1 from rfl, harmonic_succ, h46]
  norm_num
lemma h48 : harmonic 48 = (282000222059796592919 : ℚ) / 63245806209101973600 := by
  rw [show 48 = 47+1 from rfl, harmonic_succ, h47]
  norm_num
lemma h49 : harmonic 49 = (13881256687139135026631 : ℚ) / 3099044504245996706400 := by
  rw [show 49 = 48+1 from rfl, harmonic_succ, h48]
  norm_num
lemma h50 : harmonic 50 = (13943237577224054960759 : ℚ) / 3099044504245996706400 := by
  rw [show 50 = 49+1 from rfl, harmonic_succ, h49]
  norm_num
lemma h51 : harmonic 51 = (14004003155738682347159 : ℚ) / 3099044504245996706400 := by
  rw [show 51 = 50+1 from rfl, harmonic_succ, h50]
  norm_num
lemma h52 : harmonic 52 = (14063600165435720745359 : ℚ) / 3099044504245996706400 := by
  rw [show 52 = 51+1 from rfl, harmonic_succ, h51]
  norm_num
lemma h53 : harmonic 53 = (748469853272339196210427 : ℚ) / 164249358725037825439200 := by
  rw [show 53 = 52+1 from rfl, harmonic_succ, h52]
  norm_num
lemma h54 : harmonic 54 = (250503836021181200128409 : ℚ) / 54749786241679275146400 := by
  rw [show 54 = 53+1 from rfl, harmonic_succ, h53]
  norm_num
lemma h55 : harmonic 55 = (251499286680120823312889 : ℚ) / 54749786241679275146400 := by
  rw [show 55 = 54+1 from rfl, harmonic_succ, h54]
  norm_num
lemma h56 : harmonic 56 = (252476961434436524654789 : ℚ) / 54749786241679275146400 := by
  rw [show 56 = 55+1 from rfl, harmonic_succ, h55]
  norm_num
lemma h57 : harmonic 57 = (253437484000080020709989 : ℚ) / 54749786241679275146400 := by
  rw [show 57 = 56+1 from rfl, harmonic_succ, h56]
  norm_num
lemma h58 : harmonic 58 = (254381445831833111660789 : ℚ) / 54749786241679275146400 := by
  rw [show 58 = 57+1 from rfl, harmonic_succ, h57]
  norm_num
lemma h59 : harmonic 59 = (15063255090319832863132951 : ℚ) / 3230237388259077233637600 := by
  rw [show 59 = 58+1 from rfl, harmonic_succ, h58]
  norm_num
lemma h60 : harmonic 60 = (15117092380124150817026911 : ℚ) / 3230237388259077233637600 := by
  rw [show 60 = 59+1 from rfl, harmonic_succ, h59]
  norm_num
lemma h61 : harmonic 61 = (925372872575832277072279171 : ℚ) / 197044480683803711251893600 := by
  rw [show 61 = 60+1 from rfl, harmonic_succ, h60]
  norm_num
lemma h62 : harmonic 62 = (928551009361054917576341971 : ℚ) / 197044480683803711251893600 := by
  rw [show 62 = 61+1 from rfl, harmonic_succ, h61]
  norm_num
lemma h63 : harmonic 63 = (310559566510213034489743057 : ℚ) / 65681493561267903750631200 := by
  rw [show 63 = 62+1 from rfl, harmonic_succ, h62]
  norm_num
lemma h64 : harmonic 64 = (623171679694215690971693339 : ℚ) / 131362987122535807501262400 := by
  rw [show 64 = 63+1 from rfl, harmonic_succ, h63]
  norm_num
lemma h65 : harmonic 65 = (625192648726870088010174299 : ℚ) / 131362987122535807501262400 := by
  rw [show 65 = 64+1 from rfl, harmonic_succ, h64]
  norm_num
lemma h66 : harmonic 66 = (209060999005535159677640233 : ℚ) / 43787662374178602500420800 := by
  rw [show 66 = 65+1 from rfl, harmonic_succ, h65]
  norm_num
lemma h67 : harmonic 67 = (14050874595745034300902316411 : ℚ) / 2933773379069966367528193600 := by
  rw [show 67 = 66+1 from rfl, harmonic_succ, h66]
  norm_num
lemma h68 : harmonic 68 = (14094018321907827923954201611 : ℚ) / 2933773379069966367528193600 := by
  rw [show 68 = 67+1 from rfl, harmonic_succ, h67]
  norm_num
lemma h69 : harmonic 69 = (42409610330030873613929048033 : ℚ) / 8801320137209899102584580800 := by
  rw [show 69 = 68+1 from rfl, harmonic_succ, h68]
  norm_num
lemma h70 : harmonic 70 = (42535343474848157886823113473 : ℚ) / 8801320137209899102584580800 := by
  rw [show 70 = 69+1 from rfl, harmonic_succ, h69]
  norm_num
lemma h71 : harmonic 71 = (3028810706851429109067025637383 : ℚ) / 624893729741902836283505236800 := by
  rw [show 71 = 70+1 from rfl, harmonic_succ, h70]
  norm_num
lemma h72 : harmonic 72 = (9112469359293533278712889630349 : ℚ) / 1874681189225708508850515710400 := by
  rw [show 72 = 71+1 from rfl, harmonic_succ, h71]
  norm_num
lemma h73 : harmonic 73 = (667084944417653637854891458725877 : ℚ) / 136851726813476721146087646859200 := by
  rw [show 73 = 72+1 from rfl, harmonic_succ, h72]
  norm_num
lemma h74 : harmonic 74 = (668934292077295215167676426926677 : ℚ) / 136851726813476721146087646859200 := by
  rw [show 74 = 73+1 from rfl, harmonic_succ, h73]
  norm_num
lemma h75 : harmonic 75 = (670758981768141571449624262218133 : ℚ) / 136851726813476721146087646859200 := by
  rw [show 75 = 74+1 from rfl, harmonic_succ, h74]
  norm_num
lemma h76 : harmonic 76 = (672559662384108370412072783887333 : ℚ) / 136851726813476721146087646859200 := by
  rw [show 76 = 75+1 from rfl, harmonic_succ, h75]
  norm_num
lemma h77 : harmonic 77 = (61303359776139104182852056677903 : ℚ) / 12441066073952429195098876987200 := by
  rw [show 77 = 76+1 from rfl, harmonic_succ, h76]
  norm_num
lemma h78 : harmonic 78 = (61462860623241058403302042280303 : ℚ) / 12441066073952429195098876987200 := by
  rw [show 78 = 77+1 from rfl, harmonic_succ, h77]
  norm_num
lemma h79 : harmonic 79 = (4868007055309996043055960217131137 : ℚ) / 982844219842241906412811281988800 := by
  rw [show 79 = 78+1 from rfl, harmonic_succ, h78]
  norm_num
lemma h80 : harmonic 80 = (4880292608058024066886120358155997 : ℚ) / 982844219842241906412811281988800 := by
  rw [show 80 = 79+1 from rfl, harmonic_succ, h79]
  norm_num
lemma h81 : harmonic 81 = (44031838385838021258243173365847173 : ℚ) / 8845597978580177157715301537899200 := by
  rw [show 81 = 80+1 from rfl, harmonic_succ, h80]
  norm_num
lemma h82 : harmonic 82 = (44139711531918267321142140457772773 : ℚ) / 8845597978580177157715301537899200 := by
  rw [show 82 = 81+1 from rfl, harmonic_succ, h81]
  norm_num
lemma h83 : harmonic 83 = (3672441655127796364812512959533039359 : ℚ) / 734184632222154704090370027645633600 := by
  rw [show 83 = 82+1 from rfl, harmonic_succ, h82]
  norm_num
lemma h84 : harmonic 84 = (3681181948368536301765969745576439759 : ℚ) / 734184632222154704090370027645633600 := by
  rw [show 84 = 83+1 from rfl, harmonic_succ, h83]
  norm_num
lemma h85 : harmonic 85 = (3689819414629973415931738804725211919 : ℚ) / 734184632222154704090370027645633600 := by
  rw [show 85 = 84+1 from rfl, harmonic_succ, h84]
  norm_num
lemma h86 : harmonic 86 = (3698356445237207772956045432953649519 : ℚ) / 734184632222154704090370027645633600 := by
  rw [show 86 = 85+1 from rfl, harmonic_succ, h85]
  norm_num
lemma h87 : harmonic 87 = (3706795349055853229324900260857622319 : ℚ) / 734184632222154704090370027645633600 := by
  rw [show 87 = 86+1 from rfl, harmonic_succ, h86]
  norm_num
lemma h88 : harmonic 88 = (40866521918642154860585199122889549709 : ℚ) / 8076030954443701744994070304101969600 := by
  rw [show 88 = 87+1 from rfl, harmonic_succ, h87]
  norm_num
lemma h89 : harmonic 89 = (3645196481713595484337076792241271893701 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 89 = 88+1 from rfl, harmonic_succ, h88]
  norm_num
lemma h90 : harmonic 90 = (3653182778990767589396015372875328285861 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 90 = 89+1 from rfl, harmonic_succ, h89]
  norm_num
lemma h91 : harmonic 91 = (3661081314759399341652108474601318124261 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 91 = 90+1 from rfl, harmonic_succ, h90]
  norm_num
lemma h92 : harmonic 92 = (3668893996878372053122809260004199377461 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 92 = 91+1 from rfl, harmonic_succ, h91]
  norm_num
lemma h93 : harmonic 93 = (3676622671662732154792749821908124918261 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 93 = 92+1 from rfl, harmonic_succ, h92]
  norm_num
lemma h94 : harmonic 94 = (3684269126502577787295988888472646995861 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 94 = 93+1 from rfl, harmonic_succ, h93]
  norm_num
lemma h95 : harmonic 95 = (3691835092344109255246562280652279367381 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 95 = 94+1 from rfl, harmonic_succ, h94]
  norm_num
lemma h96 : harmonic 96 = (3699322246041458103739317199996707235031 : ℚ) / 718766754945489455304472257065075294400 := by
  rw [show 96 = 95+1 from rfl, harmonic_succ, h95]
  norm_num
lemma h97 : harmonic 97 = (359553024620966925518018240656745677092407 : ℚ) / 69720375229712477164533808935312303556800 := by
  rw [show 97 = 96+1 from rfl, harmonic_succ, h96]
  norm_num
lemma h98 : harmonic 98 = (360264457021270114060513483605065190394007 : ℚ) / 69720375229712477164533808935312303556800 := by
  rw [show 98 = 97+1 from rfl, harmonic_succ, h97]
  norm_num
lemma h99 : harmonic 99 = (360968703235711654233892612988250163157207 : ℚ) / 69720375229712477164533808935312303556800 := by
  rw [show 99 = 98+1 from rfl, harmonic_succ, h98]
  norm_num
lemma h100 : harmonic 100 = (14466636279520351160221518043104131447711 : ℚ) / 2788815009188499086581352357412492142272 := by
  rw [show 100 = 99+1 from rfl, harmonic_succ, h99]
  norm_num
lemma h101 : harmonic 101 = (1463919079240743966268954674710929768361083 : ℚ) / 281670315928038407744716588098661706369472 := by
  rw [show 101 = 100+1 from rfl, harmonic_succ, h100]
  norm_num
lemma h102 : harmonic 102 = (1466680552926312970266451896162877432149019 : ℚ) / 281670315928038407744716588098661706369472 := by
  rw [show 102 = 101+1 from rfl, harmonic_succ, h101]
  norm_num
lemma h103 : harmonic 103 = (151349767267338274345189261892875037217718429 : ℚ) / 29012042540587955997705808574162155756055616 := by
  rw [show 103 = 102+1 from rfl, harmonic_succ, h102]
  norm_num
lemma h104 : harmonic 104 = (151628729214843927768244125436857365638449733 : ℚ) / 29012042540587955997705808574162155756055616 := by
  rw [show 104 = 103+1 from rfl, harmonic_succ, h103]
  norm_num
lemma h105 : harmonic 105 = (759525171909485731983968522830675502275870361 : ℚ) / 145060212702939779988529042870810778780278080 := by
  rw [show 105 = 104+1 from rfl, harmonic_succ, h104]
  norm_num
lemma h106 : harmonic 106 = (760893664482154975191407476065305792641722041 : ℚ) / 145060212702939779988529042870810778780278080 := by
  rw [show 106 = 105+1 from rfl, harmonic_succ, h105]
  norm_num
lemma h107 : harmonic 107 = (81560682312293522125469128981858530591444536467 : ℚ) / 15521442759214556458772607587176753329489754560 := by
  rw [show 107 = 106+1 from rfl, harmonic_succ, h106]
  norm_num
lemma h108 : harmonic 108 = (81704399374878842092679986459517574603754626787 : ℚ) / 15521442759214556458772607587176753329489754560 := by
  rw [show 108 = 107+1 from rfl, harmonic_succ, h107]
  norm_num
lemma h109 : harmonic 109 = (8921300974621008344560891131674592385138744074343 : ℚ) / 1691837260754386654006214227002266112914383247040 := by
  rw [show 109 = 108+1 from rfl, harmonic_succ, h108]
  norm_num
lemma h110 : harmonic 110 = (812425573941376284756780362571245808659649778037 : ℚ) / 153803387341307877636928566091115101174034840640 := by
  rw [show 110 = 109+1 from rfl, harmonic_succ, h109]
  norm_num
lemma h111 : harmonic 111 = (813811190043550229600356295599093692454010452277 : ℚ) / 153803387341307877636928566091115101174034840640 := by
  rw [show 111 = 110+1 from rfl, harmonic_succ, h110]
  norm_num
lemma h112 : harmonic 112 = (815184434573383335650686014939192934428778620497 : ℚ) / 153803387341307877636928566091115101174034840640 := by
  rw [show 112 = 111+1 from rfl, harmonic_succ, h111]
  norm_num
lemma h113 : harmonic 113 = (92269644494133624806164448254219916691626018956801 : ℚ) / 17379782769567790172972927968296006432665936992320 := by
  rw [show 113 = 112+1 from rfl, harmonic_succ, h112]
  norm_num
lemma h114 : harmonic 114 = (92422098728954394895401052885520758853316071035681 : ℚ) / 17379782769567790172972927968296006432665936992320 := by
  rw [show 114 = 113+1 from rfl, harmonic_succ, h113]
  norm_num
lemma h115 : harmonic 115 = (92573227274776723505600817476549419778817513966049 : ℚ) / 17379782769567790172972927968296006432665936992320 := by
  rw [show 115 = 114+1 from rfl, harmonic_succ, h114]
  norm_num
lemma h116 : harmonic 116 = (92723052988307480317436790993517488799788772043569 : ℚ) / 17379782769567790172972927968296006432665936992320 := by
  rw [show 116 = 115+1 from rfl, harmonic_succ, h115]
  norm_num
lemma h117 : harmonic 117 = (92871598140184128096692969865041386290666258684529 : ℚ) / 17379782769567790172972927968296006432665936992320 := by
  rw [show 117 = 116+1 from rfl, harmonic_succ, h116]
  norm_num
lemma h118 : harmonic 118 = (93018884434841482250701215017315081260434614082769 : ℚ) / 17379782769567790172972927968296006432665936992320 := by
  rw [show 118 = 117+1 from rfl, harmonic_succ, h117]
  norm_num
lemma h119 : harmonic 119 = (93164933029543732588289222815367988877515840444049 : ℚ) / 17379782769567790172972927968296006432665936992320 := by
  rw [show 119 = 118+1 from rfl, harmonic_succ, h118]
  norm_num
lemma h120 : harmonic 120 = (18661952910524692834612799443020757786224277983797 : ℚ) / 3475956553913558034594585593659201286533187398464 := by
  rw [show 120 = 119+1 from rfl, harmonic_succ, h119]
  norm_num
lemma h121 : harmonic 121 = (2261572258727401391022743318199170893419670823437901 : ℚ) / 420590743023540522185944856832763355670515675214144 := by
  rw [show 121 = 120+1 from rfl, harmonic_succ, h120]
  norm_num
lemma h122 : harmonic 122 = (2265019723834151723171808439976488625843199640447853 : ℚ) / 420590743023540522185944856832763355670515675214144 := by
  rw [show 122 = 121+1 from rfl, harmonic_succ, h121]
  norm_num
lemma h123 : harmonic 123 = (2268439160769302459124539698975128978328325784148781 : ℚ) / 420590743023540522185944856832763355670515675214144 := by
  rw [show 123 = 122+1 from rfl, harmonic_succ, h122]
  norm_num
lemma h124 : harmonic 124 = (2271831021600137463335716673627006102164378329916637 : ℚ) / 420590743023540522185944856832763355670515675214144 := by
  rw [show 124 = 123+1 from rfl, harmonic_succ, h123]
  norm_num
lemma h125 : harmonic 125 = (284399468443040723439150529060208526126217806914793769 : ℚ) / 52573842877942565273243107104095419458814459401768000 := by
  rw [show 125 = 124+1 from rfl, harmonic_succ, h124]
  norm_num
lemma h126 : harmonic 126 = (284816721164294235861954045783256902471129032783061769 : ℚ) / 52573842877942565273243107104095419458814459401768000 := by
  rw [show 126 = 125+1 from rfl, harmonic_succ, h125]
  norm_num
lemma h127 : harmonic 127 = (36224297430743310519741406921577722033292201622850612663 : ℚ) / 6676878045498705789701874602220118271269436344024536000 := by
  rw [show 127 = 126+1 from rfl, harmonic_succ, h126]
  norm_num
lemma h128 : harmonic 128 = (72552921080947538317446905633815133414572988188576608701 : ℚ) / 13353756090997411579403749204440236542538872688049072000 := by
  rw [show 128 = 127+1 from rfl, harmonic_succ, h127]
  norm_num
noncomputable def shift (o : Bool) : ℝ :=
  if o then (-16811071618091732846084088270431737827926921338759786126097413044023574083070857 : ℝ) / 4000000000000000000000000000000000000000000000000000000000000000000000000000000 else (-402335143495720182899444246584910110815483700126924367402028335615165576796512809 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000
noncomputable def lowerN (o : Bool) : ℝ := if o then 541122/1000000 else 720539/1000000
noncomputable def lowerM (o : Bool) : ℝ := if o then 1230379/1000000 else 1409795/1000000
theorem harmonic_mono : Monotone (fun n => (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ, Rat.cast_add]
  have h : (0 : ℚ) ≤ ((n+1 : ℕ) : ℚ)⁻¹ := by positivity
  have hr : (0 : ℝ) ≤ (((((n+1 : ℕ) : ℚ)⁻¹) : ℚ) : ℝ) := by exact_mod_cast h
  linarith
theorem lowerN_le (o : Bool) : lowerN o ≤ (harmonic 64 : ℝ) + shift o := by
  rw [h64]
  cases o <;> norm_num [lowerN, shift]
theorem lowerM_le (o : Bool) : lowerM o ≤ (harmonic 128 : ℝ) + shift o := by
  rw [h128]
  cases o <;> norm_num [lowerM, shift]
end RHFixedWeights
