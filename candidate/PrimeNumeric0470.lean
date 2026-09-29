import PrimeAPI0470

set_option maxRecDepth 100000

set_option maxHeartbeats 10000000

open LeanCert.Core

namespace RHPrimeNumeric0470

def l2I : IntervalRat := ⟨Trial0455.lo, Trial0455.hi, by decide +kernel⟩

noncomputable def l2Expr : ℝ := Real.log 2

theorem l2_mem : l2Expr ∈ l2I := by
  exact Trial0455.log2_bounds

def l3I : IntervalRat := ⟨RHConstants0467.log3Lo, RHConstants0467.log3Hi, by decide +kernel⟩

noncomputable def l3Expr : ℝ := Real.log 3

theorem l3_mem : l3Expr ∈ l3I := by
  exact RHConstants0467.log3_bounds

def s2I : IntervalRat := ⟨RHConstants0467.sqrt2Lo, RHConstants0467.sqrt2Hi, by decide +kernel⟩

noncomputable def s2Expr : ℝ := Real.sqrt 2

theorem s2_mem : s2Expr ∈ s2I := by
  exact RHConstants0467.sqrt2_bounds

def s3I : IntervalRat := ⟨RHConstants0467.sqrt3Lo, RHConstants0467.sqrt3Hi, by decide +kernel⟩

noncomputable def s3Expr : ℝ := Real.sqrt 3

theorem s3_mem : s3Expr ∈ s3I := by
  exact RHConstants0467.sqrt3_bounds

def s17I : IntervalRat := ⟨RHConstants0467.sqrt17Lo, RHConstants0467.sqrt17Hi, by decide +kernel⟩

noncomputable def s17Expr : ℝ := Real.sqrt 17

theorem s17_mem : s17Expr ∈ s17I := by
  exact RHConstants0467.sqrt17_bounds

def oneI : IntervalRat := ⟨1 / 1, 1 / 1, by decide +kernel⟩

noncomputable def oneExpr : ℝ := 1

theorem one_mem : oneExpr ∈ oneI := by norm_num [oneExpr, oneI, IntervalRat.mem_def]

def fourI : IntervalRat := ⟨4 / 1, 4 / 1, by decide +kernel⟩

noncomputable def fourExpr : ℝ := 4

theorem four_mem : fourExpr ∈ fourI := by norm_num [fourExpr, fourI, IntervalRat.mem_def]

def seventeenI : IntervalRat := ⟨17 / 1, 17 / 1, by decide +kernel⟩

noncomputable def seventeenExpr : ℝ := 17

theorem seventeen_mem : seventeenExpr ∈ seventeenI := by norm_num [seventeenExpr, seventeenI, IntervalRat.mem_def]

def thirtyfourI : IntervalRat := ⟨34 / 1, 34 / 1, by decide +kernel⟩

noncomputable def thirtyfourExpr : ℝ := 34

theorem thirtyfour_mem : thirtyfourExpr ∈ thirtyfourI := by norm_num [thirtyfourExpr, thirtyfourI, IntervalRat.mem_def]

theorem alpha_den_lo_pos : 0 < s2I.lo := by decide +kernel

theorem alpha_den_pos : 0 < s2Expr := positive_of_mem alpha_den_lo_pos s2_mem

def alphaI : IntervalRat := ⟨2450645358671367979284754309088083453228651747747636802605615617663227746285514735357533835158217881 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 1225322679335683989642377154544041726614325873873818401302807808831613873142757367678766917579108941 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def alphaExpr : ℝ := l2Expr / s2Expr

theorem alpha_finite : alphaI.lo ≤ (posDiv l2I s2I alpha_den_lo_pos).lo ∧ (posDiv l2I s2I alpha_den_lo_pos).hi ≤ alphaI.hi := by
  decide +kernel

theorem alpha_mem : alphaExpr ∈ alphaI := widen alpha_finite (mem_posDiv alpha_den_lo_pos l2_mem s2_mem)

def splusI : IntervalRat := ⟨25615528128088302749107049279870385125735996126868102171993167865474771731688107967939318254053421483 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 51231056256176605498214098559740770251471992253736204343986335730949543463376215935878636508106842967 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def splusExpr : ℝ := oneExpr + s17Expr

theorem splus_finite : splusI.lo ≤ (IntervalRat.add oneI s17I).lo ∧ (IntervalRat.add oneI s17I).hi ≤ splusI.hi := by
  decide +kernel

theorem splus_mem : splusExpr ∈ splusI := widen splus_finite (IntervalRat.mem_add one_mem s17_mem)

def lprodI : IntervalRat := ⟨1420426488043070453207841290540108911758568417280882749401319733594314965655723878765785362916561863 / 400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 35510662201076761330196032263502722793964210432022068735032993339857874141393096969144634072914046581 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def lprodExpr : ℝ := l2Expr * splusExpr

theorem lprod_finite : lprodI.lo ≤ (IntervalRat.mul l2I splusI).lo ∧ (IntervalRat.mul l2I splusI).hi ≤ lprodI.hi := by
  decide +kernel

theorem lprod_mem : lprodExpr ∈ lprodI := widen lprod_finite (IntervalRat.mem_mul l2_mem splus_mem)

theorem lam_den_lo_pos : 0 < fourI.lo := by decide +kernel

theorem lam_den_pos : 0 < fourExpr := positive_of_mem lam_den_lo_pos four_mem

def lamI : IntervalRat := ⟨8877665550269190332549008065875680698491052608005517183758248334964468535348274242286158518228511643 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 4438832775134595166274504032937840349245526304002758591879124167482234267674137121143079259114255823 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def lamExpr : ℝ := lprodExpr / fourExpr

theorem lam_finite : lamI.lo ≤ (posDiv lprodI fourI lam_den_lo_pos).lo ∧ (posDiv lprodI fourI lam_den_lo_pos).hi ≤ lamI.hi := by
  decide +kernel

theorem lam_mem : lamExpr ∈ lamI := widen lam_finite (mem_posDiv lam_den_lo_pos lprod_mem four_mem)

def sdiffI : IntervalRat := ⟨128768943743823394501785901440259229748528007746263795656013664269050456536623784064121363491893157033 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 64384471871911697250892950720129614874264003873131897828006832134525228268311892032060681745946578517 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def sdiffExpr : ℝ := seventeenExpr - s17Expr

theorem sdiff_finite : sdiffI.lo ≤ (IntervalRat.sub seventeenI s17I).lo ∧ (IntervalRat.sub seventeenI s17I).hi ≤ sdiffI.hi := by
  decide +kernel

theorem sdiff_mem : sdiffExpr ∈ sdiffI := widen sdiff_finite (IntervalRat.mem_sub seventeen_mem s17_mem)

theorem p_den_lo_pos : 0 < thirtyfourI.lo := by decide +kernel

theorem p_den_pos : 0 < thirtyfourExpr := positive_of_mem p_den_lo_pos thirtyfour_mem

def pI : IntervalRat := ⟨473415234352291891550683461177423638781352969655381601676520824518567854914058029647505012837842489 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3787321874818335132405467689419389110250823757243052813412166596148542839312464237180040102702739913 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def pExpr : ℝ := sdiffExpr / thirtyfourExpr

theorem p_finite : pI.lo ≤ (posDiv sdiffI thirtyfourI p_den_lo_pos).lo ∧ (posDiv sdiffI thirtyfourI p_den_lo_pos).hi ≤ pI.hi := by
  decide +kernel

theorem p_mem : pExpr ∈ pI := widen p_finite (mem_posDiv p_den_lo_pos sdiff_mem thirtyfour_mem)

def deltaI : IntervalRat := ⟨3976374832926454373979499447699513792033749112510243578547017099638013042777244771571090847912075879 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 994093708231613593494874861924878448008437278127560894636754274909503260694311192892772711978018971 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def deltaExpr : ℝ := lamExpr - alphaExpr

theorem delta_finite : deltaI.lo ≤ (IntervalRat.sub lamI alphaI).lo ∧ (IntervalRat.sub lamI alphaI).hi ≤ deltaI.hi := by
  decide +kernel

theorem delta_mem : deltaExpr ∈ deltaI := widen delta_finite (IntervalRat.mem_sub lam_mem alpha_mem)

theorem mu_den_lo_pos : 0 < s3I.lo := by decide +kernel

theorem mu_den_pos : 0 < s3Expr := positive_of_mem mu_den_lo_pos s3_mem

def muI : IntervalRat := ⟨317142050298781988593193886272324527599768350964600406378080189359268632213952437225601387888891551 / 500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3171420502987819885931938862723245275997683509646004063780801893592686322139524372256013878888915511 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def muExpr : ℝ := l3Expr / s3Expr

theorem mu_finite : muI.lo ≤ (posDiv l3I s3I mu_den_lo_pos).lo ∧ (posDiv l3I s3I mu_den_lo_pos).hi ≤ muI.hi := by
  decide +kernel

theorem mu_mem : muExpr ∈ muI := widen mu_finite (mem_posDiv mu_den_lo_pos l3_mem s3_mem)

def pmuI : IntervalRat := ⟨480447609808525497071526778171700652862883972917175168306165941992823418896678909105869887579835011 / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 2402238049042627485357633890858503264314419864585875841530829709964117094483394545529349437899175057 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def pmuExpr : ℝ := pExpr * muExpr

theorem pmu_finite : pmuI.lo ≤ (IntervalRat.mul pI muI).lo ∧ (IntervalRat.mul pI muI).hi ≤ pmuI.hi := by
  decide +kernel

theorem pmu_mem : pmuExpr ∈ pmuI := widen pmu_finite (IntervalRat.mem_mul p_mem mu_mem)

def dmuI : IntervalRat := ⟨10319215838902094145843377173146004344029116131802251706108620886823385687056293516083118605689906899 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 5159607919451047072921688586573002172014558065901125853054310443411692843528146758041559302844953453 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def dmuExpr : ℝ := deltaExpr + muExpr

theorem dmu_finite : dmuI.lo ≤ (IntervalRat.add deltaI muI).lo ∧ (IntervalRat.add deltaI muI).hi ≤ dmuI.hi := by
  decide +kernel

theorem dmu_mem : dmuExpr ∈ dmuI := widen dmu_finite (IntervalRat.mem_add delta_mem mu_mem)

def denominatorI : IntervalRat := ⟨6360726943972360815600505532002253804171767998194063773819725298393751390769844030806234021794540977 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 12721453887944721631201011064004507608343535996388127547639450596787502781539688061612468043589081963 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def denominatorExpr : ℝ := dmuExpr + pmuExpr

theorem denominator_finite : denominatorI.lo ≤ (IntervalRat.add dmuI pmuI).lo ∧ (IntervalRat.add dmuI pmuI).hi ≤ denominatorI.hi := by
  decide +kernel

theorem denominator_mem : denominatorExpr ∈ denominatorI := widen denominator_finite (IntervalRat.mem_add dmu_mem pmu_mem)

def pdeltaI : IntervalRat := ⟨1505981138721946330923217418803787747474741672097358851893057925850391429513809453997660033140872763 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 752990569360973165461608709401893873737370836048679425946528962925195714756904726998830016570436383 / 5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def pdeltaExpr : ℝ := pExpr * deltaExpr

theorem pdelta_finite : pdeltaI.lo ≤ (IntervalRat.mul pI deltaI).lo ∧ (IntervalRat.mul pI deltaI).hi ≤ pdeltaI.hi := by
  decide +kernel

theorem pdelta_mem : pdeltaExpr ∈ pdeltaI := widen pdelta_finite (IntervalRat.mem_mul p_mem delta_mem)

def numeratorI : IntervalRat := ⟨119402486511393119697538318277244647361461683439035335720905089033351044721179848253211018315735767 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 955219892091144957580306546217957178891693467512282685767240712266808357769438786025688146525886139 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def numeratorExpr : ℝ := pdeltaExpr * muExpr

theorem numerator_finite : numeratorI.lo ≤ (IntervalRat.mul pdeltaI muI).lo ∧ (IntervalRat.mul pdeltaI muI).hi ≤ numeratorI.hi := by
  decide +kernel

theorem numerator_mem : numeratorExpr ∈ numeratorI := widen numerator_finite (IntervalRat.mem_mul pdelta_mem mu_mem)

theorem gamma_den_lo_pos : 0 < denominatorI.lo := by decide +kernel

theorem gamma_den_pos : 0 < denominatorExpr := positive_of_mem gamma_den_lo_pos denominator_mem

def gammaI : IntervalRat := ⟨150174642066083895426607251308229098793141597778867718496504365630293928929085519195416301881165871 / 2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 750873210330419477133036256541145493965707988894338592482521828151469644645427595977081509405829359 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def gammaExpr : ℝ := numeratorExpr / denominatorExpr

theorem gamma_finite : gammaI.lo ≤ (posDiv numeratorI denominatorI gamma_den_lo_pos).lo ∧ (posDiv numeratorI denominatorI gamma_den_lo_pos).hi ≤ gammaI.hi := by
  decide +kernel

theorem gamma_mem : gammaExpr ∈ gammaI := widen gamma_finite (mem_posDiv gamma_den_lo_pos numerator_mem denominator_mem)

def sumI : IntervalRat := ⟨15220506556244830104412885791322171250486419627297525311319852122149841179627322986798186276006342663 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 3805126639061207526103221447830542812621604906824381327829963030537460294906830746699546569001585667 / 2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def sumExpr : ℝ := lamExpr + muExpr

theorem sum_finite : sumI.lo ≤ (IntervalRat.add lamI muI).lo ∧ (IntervalRat.add lamI muI).hi ≤ sumI.hi := by
  decide +kernel

theorem sum_mem : sumExpr ∈ sumI := widen sum_finite (IntervalRat.mem_add lam_mem mu_mem)

def primeI : IntervalRat := ⟨1808704168239301328409981191847628219565088954800398339854666286749796441872736923852638095825064163 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 14469633345914410627279849534781025756520711638403186718837330293998371534981895390821104766600513313 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, by decide +kernel⟩

noncomputable def primeExpr : ℝ := sumExpr - gammaExpr

theorem prime_finite : primeI.lo ≤ (IntervalRat.sub sumI gammaI).lo ∧ (IntervalRat.sub sumI gammaI).hi ≤ primeI.hi := by
  decide +kernel

theorem prime_mem : primeExpr ∈ primeI := widen prime_finite (IntervalRat.mem_sub sum_mem gamma_mem)

def primeLo : ℚ := 1808704168239301328409981191847628219565088954800398339854666286749796441872736923852638095825064163 / 1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def primeHi : ℚ := 14469633345914410627279849534781025756520711638403186718837330293998371534981895390821104766600513313 / 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem prime_bounds : (primeLo : ℝ) ≤ primeExpr ∧ primeExpr ≤ (primeHi : ℝ) := prime_mem

theorem prime_width : primeHi - primeLo ≤ (1 : ℚ) / 10^95 := by decide +kernel

theorem denominator_pos : 0 < deltaExpr + muExpr + pExpr * muExpr := gamma_den_pos

end RHPrimeNumeric0470










































































































