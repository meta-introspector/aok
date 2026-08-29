A waste metric for seven product stacks
Memory, energy and water per unit of served work — machine-checked accounting
on stated assumptions.

A list of "the infra behind products you use" says what a fleet is made of. It
says nothing about what the fleet wastes, and waste is the only thing a bill and
a cooling tower actually see. This layer attaches three metrics to each of seven
named stacks and proves the arithmetic:

memory waste — the fraction of provisioned RAM that is not distinct
useful state;
energy waste — the fraction of the meter that is idle draw plus facility
overhead;
water waste — litres a month attributable to those wasted watts, on site
through evaporative cooling and off site in generation, normalised to litres
per million requests.
file	what is in it
RequestProject/Theory/InfraWaste.lean	the accounting. No company, no number.
RequestProject/Data/PlatformStacks.lean	the seven stacks, as assumptions.
RequestProject/InfraWasteLedger.lean	the certified arithmetic.
RequestProject/InfraWasteDemo.lean	the same figures printed as tables.
The honest caveat, first
Nobody publishes node counts, resident working sets, idle draw, site water
usage effectiveness or request volume for these services. The parameters in
Data/PlatformStacks.lean are constructed to be representative of the
architecture — a JVM store at RF=3 with a cache tier, a shard-per-core native
store, an edge estate, a tropical colocation — and are not descriptive of any
operator's fleet. Nothing here is a measurement of Spotify, Shopify, Discord,
Netflix, Cloudflare, Dropbox or Grab. What is proved is that given those
inputs, these waste figures follow, and that they move in the stated directions
when the inputs move. Replace the data file and every theorem in the ledger
changes; not one theorem in Theory/ does.

The three identities
Memory (Stack.wasted_decomposition): the gap between provisioned RAM and
distinct useful state is exactly three things —

provisioned = distinct + copies + runtime overhead + headroom
Power (Stack.facilityPower_decomposition): the meter splits into three —

facility = dynamic + idle + cooling
with waste defined as the last two. Stack.wastePower_eq_zero_iff says the
waste term vanishes exactly when a node draws nothing at rest and the building
is free to run, i.e. never.

Water (Stack.wastedLitres_eq): water waste is not an independent quantity at
all — it is wasted kilowatt-hours times the site's and the grid's intensity.
Stack.wastedLitres_dry keeps the two channels apart: an air-cooled site still
consumes the generator's water.

The table
Ranked by the headline metric, wasted litres per million requests. Every figure
is a theorem in InfraWasteLedger.lean; the exact rationals are in the ticks
and the decimals are those rationals rounded.

stack	memory waste	energy waste	wasted L / M-req	total L / M-req
Cloudflare — Pingora + Rust	103/128 = 80.47%	451/901 = 50.06%	1218151/800000 = 1.523	2433601/800000 = 3.042
Discord — ScyllaDB + Rust	1679/2304 = 72.87%	1611/3151 = 51.13%	66680901/40000000 = 1.667	3.261
Spotify — GKE + Kubernetes	103/128 = 80.47%	709/1199 = 59.13%	51757/12500 = 4.141	7.002
Shopify — GKE + MySQL	103/128 = 80.47%	43/68 = 63.24%	900893/125000 = 7.207	11.397
Netflix — Cassandra + EVCache	329/384 = 85.68%	257/437 = 58.81%	2420169/312500 = 7.745	13.169
Dropbox — Envoy + gRPC	11/16 = 68.75%	581/981 = 59.23%	10476011/937500 = 11.174	18.868
Grab — Kafka + EKS	27/32 = 84.38%	551/791 = 69.66%	120669/5000 = 24.134	173229/5000 = 34.646
Backing theorems: *_memoryWaste, *_energyWaste, *_wastedWater,
grab_totalWater, cloudflare_totalWater; the order itself is
water_ranking, and the spread between the ends is water_spread,
264480/16687 ≈ 15.85×.

Two order facts are worth stating on their own:

all_waste_over_half — every stack in the table burns more than half its
meter on idling and cooling. The best of the seven is the edge estate at
50.06%, the worst the tropical log at 69.66%.
memory_ranking — every stack wastes more than two thirds of its RAM
against distinct useful state. Best is the mesh at 68.75%, worst the
managed-runtime store with a cache tier at 85.68%.
The seven together
quantity	a month	theorem
electricity	109909457/10 kWh ≈ 10.99 GWh	fleet_monthlyKWh
of which wasted	62884317/10 kWh ≈ 6.29 GWh	fleet_wastedKWh
water	11668347959/500 L ≈ 23.34 million L	fleet_monthlyLitres
of which wasted	6783217159/500 L ≈ 13.57 million L	fleet_wastedLitres
electricity bought by idling and cooling	596900633/1000 ≈ $596,900.63	fleet_wastedUSD
RAM that is not distinct state	7915600 GB	fleet_wastedGB
fleet_water_waste_share: 92920783/159840383 ≈ 58.13% of the water is
bought by idle machines and cooling overhead, not by served requests.

Three sensitivities
The rewrite that changes nothing (native_runtime_moves_nothing). Move the
cached store from a managed runtime to a native one — heap multiplier 2 down
to 23/20, nothing else touched. The working set falls from 1320000 GB to
759000 GB. Every one of those 561000 GB becomes headroom, and the memory
waste figure is identical, as is the water. The RAM had already been bought:
a rewrite converts runtime overhead into headroom and nothing else. Only
decommissioning boxes, or serving more from them, moves the metric.

Filling the machines does move it (packing_cuts_water). Doubling
utilization on the same boxes, and therefore serving twice the requests, takes
the energy waste fraction from 709/1199 to 379/869 — 59.13% to 43.61% — and
the wasted water from 51757/12500 to 27667/12500 litres per million
requests, a 46.55% cut on the same hardware.

So does moving the site (geography_cuts_water). The same JVM log,
unchanged in every software respect, on a temperate campus instead of a tropical
one: wasted water per million requests falls from 120669/5000 to
167097/20000 litres — 24.134 to 8.355, a cut of 315579/20000 litres, 65.4%,
bought entirely with geography.

The three together are the point of the layer. Of the levers available, the one
that reads as an engineering achievement — rewriting the runtime — is the only
one that moves no metric at all, because the waste it removes was already paid
for. Packing and siting, which are procurement decisions rather than code, move
the water by a factor of two and three.

Comparative statics, proved once in Theory/
lever	direction	theorem
more copies resident	less headroom	headroom_antitone_replication
fatter runtime	less headroom	headroom_antitone_runtime
more RAM for the same data	more waste	wastedGB_mono_ram
higher utilization	lower energy waste fraction	energyWasteFraction_antitone_utilization
worse PUE	more wasted watts	wastePower_mono_pue
more idle draw	more wasted water	wastedLitres_mono_idle
more requests on the same fleet	fewer kWh per request	kWhPerMillionRequests_antitone
Every division in the theory carries its positivity hypothesis in
Stack.WellFormed, and each of the seven stacks and the three variants is
proved well formed in the ledger before any of its figures is quoted.

The chart, and the paper
A chart cannot draw an exact rational, so
RequestProject/InfraWasteInfographic.lean closes the last gap: the seven
printed bar labels are each proved within half a unit in the last place of the
exact value (bar_cloudflare … bar_grab, using RoundsTo2dp), and so are the
15.85× spread (spread_rounds) and the 58% water share
(water_share_rounds). The two savings badges are proved as exact ratios and
then bounded: the utilization cut is 24090/51757, between 46% and 47%, so the
printed −46% is a floor (packing_cut_fraction); the siting cut is
315579/482676, which rounds to the printed −65% (geography_cut_fraction).

docs/infra-waste.pdf (source docs/infra-waste.tex, built with
tectonic -X compile docs/infra-waste.tex) is the short paper: the model, the
parameter table, one worked derivation, and the theorem name behind every
figure on the chart. scripts/check_constants.py checks that every exact
rational typeset in it occurs in a Lean statement.
