# Hosting providers for the two computation nodes and five database nodes

Date of research: 11 November 2026. All prices and measurements were looked up on that date unless a line says otherwise. Prices are in the currency the provider publishes and exclude VAT.

## How to read this report

Three kinds of statement appear below, and they are not equally reliable.

- **Measured today.** Round-trip times marked "measured" were taken for this report on 11 Nov 2026 between about 21:50 and 22:20 UTC, using the public Globalping measurement network (https://globalping.io). A probe hosted inside provider A sent 8 ICMP pings to a public test host of provider B. Every row is in Appendix A with its measurement ID. These are real measurements between the named networks, but they are one evening snapshot, 8 packets each, to a provider's test host rather than to a rented server, and the probe's city label comes from a geolocation database.
- **Fetched today.** Prices and policy wording with a URL were read from that page today.
- **Not verified today.** Several providers' pricing pages refused automated fetches (Scaleway, Vultr, UpCloud, Leaseweb, FDCservers). Where I rely on a search-result snippet, a third-party listing or general knowledge, the line says so. Treat those as leads to confirm in the provider's order form.

Legal and jurisdictional notes are a summary of publicly known law, not legal advice, and were not re-verified against primary legal sources today except where a URL is given.

## Summary of findings

1. **Sub-millisecond paths between independent providers exist in several metros.** Measured examples: Amsterdam Leaseweb to Scaleway 0.31–0.97 ms; Frankfurt Leaseweb to Clouvider 0.63–0.90 ms; Nuremberg netcup to Hetzner 0.40–0.86 ms; Ashburn Clouvider to Hetzner 0.41–0.59 ms; Paris Vultr to Scaleway 0.64–0.86 ms.
2. **Traffic cost is not the constraint once hyperscale clouds are excluded.** 50 TB a month is an average of about 150 Mbit/s. Bare-metal providers either do not meter (OVHcloud, Hetzner on 1 Gbit/s, netcup) or include 20–100 TB on a 10 Gbit/s port (Hetzner, Clouvider, Worldstream). The same 20 TB costs about $1,800 a month each way at typical hyperscaler internet egress rates.
3. **Jurisdictional separation costs latency.** No cross-border pair measured under 2 ms. The best was Tallinn to Hetzner Helsinki at 2.0–2.2 ms. The next tier is 4–6 ms (Luxembourg–Frankfurt 4.3 ms, Strasbourg–Frankfurt 4.5 ms, Gravelines–London 4.0 ms, Zurich–Frankfurt 5.8 ms).
4. **The cheapest sub-millisecond pair, Hetzner plus netcup in Nuremberg, is not two independent infrastructures.** PeeringDB lists netcup's Nuremberg presence inside "Hetzner Online NBG1", so Hetzner operates the building for both.

What the round-trip time means for the two operations:

| Round-trip time | 2,800 round trips | 11,500 round trips |
|---|---|---|
| 0.5 ms | 1.4 s | 5.8 s |
| 1.0 ms | 2.8 s | 11.5 s |
| 2.0 ms | 5.6 s | 23 s |
| 4.5 ms | 12.6 s | 52 s |
| 6.0 ms | 16.8 s | 69 s |

WireGuard adds per-packet processing but no extra round trips; measure it rather than assume (section 5).

## 1. Shortlisted pairs for the computation nodes

Traffic cost columns are per provider per month for that provider's outbound traffic. Each provider bills only its own egress, so the pair cost is the sum of both.

### Pair A — Frankfurt: Clouvider + Leaseweb (alternatives: Vultr, FDCservers)

- **Locations.** Clouvider lists itself in Equinix FR4, FR5, FR6, FR7 and FR8 (PeeringDB, AS62240). Leaseweb's Frankfurt site is FRA-10; Leaseweb's ASNs had no facility rows in the PeeringDB data I pulled, so its building is not confirmed here. Vultr lists Digital Realty Frankfurt FRA1-27 (AS20473). FDCservers lists Equinix FR6 and FR8 (AS30058). Source: https://www.peeringdb.com/api/netfac (full table downloaded today, filtered by ASN).
- **Measured round trip.** Leaseweb to Clouvider 0.63–0.90 ms (5 probe runs); Clouvider to Leaseweb 0.62 ms; Vultr to Clouvider 0.55–0.67 ms; Clouvider to Vultr 0.65 ms; Clouvider to FDCservers 0.49 ms; Leaseweb to FDCservers 0.82–0.84 ms; Leaseweb to Vultr 0.81–0.90 ms.
- **Clouvider pricing (fetched).** 10 Gbit/s servers with 50 TB included: Xeon E-2388G 8 cores, 32–128 GB RAM, 960 GB NVMe, $167/month in Frankfurt and Amsterdam. Dual EPYC 7313 (2x16 cores), 128 GB–1 TB RAM, 100 TB on 10 Gbit/s, $471/month in Amsterdam, Frankfurt and New York. The page does not state the overage rate or the price of the RAM upgrades. https://www.clouvider.com/10gbps-dedicated-servers/
- **Leaseweb pricing (not verified today).** The site returned an empty page to automated fetches. A search snippet of Leaseweb's own listing showed a server with 100 TB on a 1 Gbit/s port at €182.99/month and a 10 Gbit/s unmetered server at €1,139.99/month in Amsterdam, and "from €139.91" in Germany (https://www.leaseweb.com/de/bare-metal-server/alle-server). The price of a metered 10 Gbit/s port is unknown. A competitor's blog claims overage of $0.05/GB; unverified.
- **Vultr pricing (not verified on Vultr's page).** Bare metal EPYC 7443P, 24 cores, 256 GB, 10 TB included, $725/month (third-party 2026 overview). Overage $0.01/GB per Vultr's billing documentation: https://docs.vultr.com/support/platform/billing/what-is-the-bandwidth-overage-rate
- **Fit.** Clouvider's 8-core models are below the 12-core requirement; the dual EPYC 7313 at $471 meets it. Leaseweb or Vultr hardware needs a configurator check.
- **Traffic cost per month (5 / 20 / 50 TB out).** Clouvider dual EPYC (100 TB included): $0 / $0 / $0. Clouvider 50 TB models: $0 / $0 / $0 at exactly the allowance, overage unknown beyond it. Leaseweb with a 100 TB package: €0 / €0 / €0, but on a 1 Gbit/s port. Vultr: $0 / about $100 / about $400.

### Pair B — Amsterdam: Scaleway + Leaseweb (alternative: Vultr)

- **Locations.** Scaleway lists Iron Mountain AMS-1 (Haarlem), Digital Realty AMS9 and AMS17 (AS12876). Vultr lists Iron Mountain AMS-1 (AS20473). Leaseweb's AMS-01 is, from general knowledge, also on the Haarlem campus; not confirmed from PeeringDB today. Latitude.sh, Hivelocity, NovoServe, Worldstream and Servers.com also list Iron Mountain AMS-1, which makes that building the densest cluster of independent bare-metal providers found in this research.
- **Measured round trip.** Leaseweb to Scaleway 0.31, 0.40, 0.43, 0.80, 0.83 ms (five probes); Scaleway to Leaseweb 0.77–1.04 ms; Vultr to Scaleway 0.31–0.93 ms; Leaseweb to Vultr 0.30–0.77 ms; Vultr to Leaseweb 0.78–0.80 ms.
- **Scaleway pricing (not verified on Scaleway's page; it returned 403).** Third-party listings dated April 2026: Elastic Metal EM-I120E, EPYC 8024P 8 cores, 64 GB, 2x960 GB NVMe, €129.99/month; EM-I210E €239.99/month. Scaleway's Iridium page is quoted as "Public Bandwidth 1 Gbps to 25 Gbps". I believe Elastic Metal traffic is unmetered but could not confirm it today, nor the price of the faster ports. https://www.scaleway.com/en/elastic-metal/iridium/
- **Leaseweb and Vultr pricing.** As in pair A.
- **Traffic cost per month (5 / 20 / 50 TB out).** Scaleway: €0 if unmetered (to confirm). Leaseweb 100 TB package: €0. Vultr: $0 / about $100 / about $400.

### Pair C — Nuremberg: Hetzner + netcup (cheapest; weak independence)

- **Locations.** Hetzner NBG1, Nuremberg. PeeringDB lists netcup (AS197540) in "Hetzner Online NBG1 (Nuremberg)" and nowhere else in Germany. netcup's parent Anexia (AS47147) is listed in the same facility.
- **Measured round trip.** netcup to Hetzner NBG1: 0.40, 0.40, 0.40, 0.42, 0.68, 0.82 ms (six probes over two runs). netcup to Hetzner Falkenstein 3.0 ms, so the Hetzner node must be ordered in NBG1, not FSN1. Contabo Nuremberg to Hetzner NBG1 was 9.3 ms, which shows that "same city" alone proves nothing.
- **Hetzner pricing (fetched).** AX102, Ryzen 9 7950X3D 16 cores, 128 GB DDR5 ECC, 2x1.92 TB NVMe, from €159/month, setup €129. AX162, EPYC 9454P 48 cores, 128 GB, from €319/month, setup €304. https://www.hetzner.com/dedicated-rootserver/matrix-ax/ — 1 Gbit/s port: "Traffic usage is unlimited and free of charge." 10 Gbit/s uplink: 20 TB outbound included, then €1.00/TB, "no bandwidth limitation", inbound free; the Robot firewall is not available with it. https://docs.hetzner.com/robot/dedicated-server/network/10g-uplink/ and https://docs.hetzner.com/robot/general/traffic/ — monthly fee for the 10 Gbit/s uplink €43 per a search snippet of Hetzner's add-on price list (https://docs.hetzner.com/robot/general/pricing/price-list-for-additional-products); an older document says €51.17. Confirm in the configurator.
- **netcup pricing (fetched).** These are virtual machines with dedicated cores, not bare metal. RS 8000 G12.5: 16 dedicated EPYC 9645 cores, 64 GB, 1 TB NVMe, €148.42/month. RS 16000 G12.5: 24 cores, 128 GB, €289.46/month, on request only. Network card "up to 2.5 Gbit/s". https://www.netcup.com/en/server/root-server — the page states no traffic terms. A forum post quoting netcup says traffic is free, but the port can be limited to 200 Mbit/s if more than 120 TB is used in a month and more than 1 Gbit/s is used continuously for over 60 minutes (https://lowendtalk.com/discussion/comment/3810691/; second-hand).
- **Traffic cost per month (5 / 20 / 50 TB out).** Hetzner 10 Gbit/s: €0 / €0 / €30 on top of the uplink fee. Hetzner 1 Gbit/s: €0. netcup: €0.
- **Why it ranks below A and B despite the price.** Hetzner has physical access to both machines; both companies are German; the netcup side is a virtual machine on shared hosts with a 2.5 Gbit/s ceiling.

### Pair D — Frankfurt: OVHcloud (Limburg) + Leaseweb, Vultr or FDCservers (best unmetered option)

- **Locations.** OVHcloud's German data centre is at Limburg an der Lahn, about 60 km from Frankfurt, with network presence in Equinix FR5 and Digital Realty Frankfurt (PeeringDB, AS16276).
- **Measured round trip.** OVH to Leaseweb 1.49–1.84 ms (six probe results, one labelled Limburg); OVH to Vultr 1.47–1.61 ms; OVH to FDCservers 1.41–1.42 ms. OVH to Clouvider was 9.3 ms on both probes, so that combination is ruled out unless the reverse path proves better.
- **OVHcloud pricing (fetched).** Advance-3 (2024), EPYC 4464P 12 cores, 64 GB DDR5 ECC, 2x960 GB NVMe, public bandwidth "3 Gbps, unmetered and guaranteed", $236/month plus $236 installation. https://www.ovhcloud.com/en/bare-metal/advance/ — "Your public bandwidth is unlimited and unmetered"; the same page warns that if usage exceeds limits the service may continue with reduced quality. https://www.ovhcloud.com/en/bare-metal/bandwidth/ — the Scale range offers 1 to 10 Gbit/s public bandwidth from $689/month (US page, search snippet): https://us.ovhcloud.com/bare-metal/scale/
- **Traffic cost per month.** OVHcloud: $0 at any of the three volumes. Partner as in pair A.

### Pair E — Northern Virginia: Clouvider + Hetzner (lowest measured latency; Hetzner side is a cloud VM)

- **Locations.** Clouvider lists Equinix Ashburn (AS62240). Hetzner's Ashburn site offers cloud servers only, no dedicated servers.
- **Measured round trip.** Clouvider to Hetzner 0.41, 0.43, 0.49 ms; Leaseweb (Manassas) to Hetzner 1.18–1.34 ms; Leaseweb to Clouvider 1.18 ms; OVH (Vint Hill) to Hetzner 1.71–2.04 ms; OVH to Leaseweb 2.15–2.17 ms.
- **Pricing.** Hetzner cloud prices rose on 15 June 2026; secondary sources give CCX33 (8 dedicated vCPU, 32 GB) €140.99 and CCX63 (48 vCPU, 192 GB) €853.49 in the US, with 1–8 TB of traffic included (https://wz-it.com/en/blog/hetzner-price-increase-june-2026-cpx-ccx-alternatives/). I could not confirm the US overage rate. Hetzner bills only outgoing traffic (https://docs.hetzner.com/cloud/billing/faq/). Clouvider's 10 Gbit/s page lists no Ashburn offers.
- **Assessment.** Good latency, poor fit: a virtual machine with a small traffic allowance on one side, and every party is on US soil.

### Pair F — Paris: Scaleway + Vultr

- **Locations.** Scaleway DC3 Vitry-sur-Seine and DC5 Saint-Ouen-l'Aumône, with a point of presence at Telehouse Paris 2 (AS12876). Vultr lists Digital Realty Paris PAR2 (AS20473).
- **Measured round trip.** Vultr to Scaleway 0.64, 0.66, 0.71, 0.72 ms; Scaleway to Vultr 1.16–1.33 ms (the target differs, hence the asymmetry). Scaleway Paris to OVH Roubaix is 4.7–6.3 ms, so OVH's French data centres do not pair with Paris.
- **Pricing.** As above for both. Not verified today.

### Pair G — Helsinki: Hetzner + UpCloud

- **Locations.** Hetzner HEL1 at Tuusula. UpCloud lists Equinix HE6 Espoo and Telia Helsinki (AS202053).
- **Measured round trip.** UpCloud to Hetzner HEL1 0.96 and 1.05 ms; FlokiNET Helsinki to Hetzner 0.97 ms.
- **Pricing.** Hetzner as in pair C. UpCloud has zero-cost egress under a Fair Transfer Policy: past the limit "we may throttle the bandwidth on the cloud services down to 100 Mbit/s" (https://upcloud.com/docs/products/networking/network-transfer/). That throttle rules UpCloud out for a computation node at tens of terabytes unless the allowance of a large plan covers it; ask before ordering.

### Other metros measured (all parties in the United States, or weak results)

| Metro | Pair | Measured round trip | Note |
|---|---|---|---|
| Los Angeles | ReliableSite to Vultr | 0.28 ms | Also OVH to Vultr 0.42 ms, HostHatch to Vultr 0.52 ms |
| Dallas | Datacamp (DataPacket) to Vultr | 0.37 ms | Linode to Vultr 0.97 ms |
| Chicago | FDCservers to Vultr | 0.94 ms | Hivelocity to Vultr 1.76 ms |
| New York / New Jersey | ReliableSite (Piscataway) to Vultr | 0.88 ms | HostHatch to Clouvider New York 0.90 ms; others about 2.1 ms |
| Silicon Valley | xTom, DigitalOcean to Vultr | 1.0–1.1 ms | |
| London | OVH to Clouvider | 1.30 ms and 4.06 ms | Leaseweb to Vultr 1.68 ms; nothing under 1 ms found |
| Singapore | OVH, DigitalOcean, Linode to Vultr | minimum 1.1–1.5 ms, average 5–18 ms | Large jitter in every run; not recommended on this evidence |

I did not research prices for the US-only pairs; they add nothing on jurisdiction and the European pairs match them on latency.

## 2. Comparison tables

Cost is the estimated total for both servers plus traffic at 20 TB each way, using the cheapest configuration found that meets 12 cores and 64 GB. "?" marks a component I could not price from the provider's own page.

### Ranked by latency, cost and evidence

| Pair | Metro | Measured round trip | Cost at 20 TB each way, per month | Port speed available | Company jurisdictions | Data-centre jurisdiction | Exposure to compelled or informal cooperation | Confidence |
|---|---|---|---|---|---|---|---|---|
| A. Clouvider + Leaseweb | Frankfurt | 0.6–0.9 ms | $471 + Leaseweb ? (order of €180–300 on 1 Gbit/s) ; traffic 0 | 10 Gbit/s Clouvider; Leaseweb 10 Gbit/s price unknown | UK; Netherlands (German sales entity) | Germany for both | One state (Germany) can reach both machines; UK law reaches Clouvider as a company | Latency high; Leaseweb price low |
| B. Scaleway + Leaseweb | Amsterdam | 0.3–1.0 ms | about €130–240 + Leaseweb ? ; traffic 0 if Scaleway unmetered | Scaleway up to 25 Gbit/s (price unknown) | France (Iliad group); Netherlands | Netherlands for both | One state (Netherlands) can reach both; probably the same campus | Latency high; prices low |
| C. Hetzner + netcup | Nuremberg | 0.4–0.9 ms | €159 + €43 + €148 = about €350; traffic 0 | 10 Gbit/s Hetzner; 2.5 Gbit/s netcup | Germany; Germany (Austrian parent Anexia) | Germany, same building, operated by Hetzner | One state and one facility operator reach both | Latency high; prices high; independence fails |
| D. OVHcloud + Leaseweb / Vultr / FDCservers | Frankfurt area | 1.4–1.9 ms | $236 + partner ? ; traffic 0 at OVH | 3 Gbit/s OVH Advance, 10 Gbit/s on Scale | France; Netherlands or US | Germany for both | One state (Germany); adding Vultr or FDCservers adds US reach | Latency high; OVH price high |
| E. Clouvider + Hetzner cloud | Ashburn | 0.4–0.6 ms | not priced; Hetzner traffic metered | 10 Gbit/s Clouvider | UK; Germany (US subsidiary) | United States for both | US law reaches both machines directly | Latency medium (3 probes); prices low |
| F. Scaleway + Vultr | Paris | 0.6–1.3 ms | about €130–240 + $725 + about $100 traffic | up to 25 Gbit/s Scaleway | France; US | France for both | France reaches both; US reaches Vultr | Latency medium; prices low |
| G. Hetzner + UpCloud | Helsinki | 1.0 ms | €202 + UpCloud ? ; UpCloud may throttle | 10 Gbit/s Hetzner | Germany; Finland | Finland for both | One state (Finland) reaches both | Latency medium; UpCloud fit doubtful |

### Ranked with jurisdictional separation first

| Rank | Pair | Company jurisdictions | Data-centre jurisdictions | Measured round trip | Latency cost against the best same-metro pair (about 0.5 ms) | Assessment |
|---|---|---|---|---|---|---|
| 1 | Hetzner HEL1 (or UpCloud) + a Tallinn provider such as WaveCom | Germany or Finland; Estonia | Finland; Estonia | 2.0–2.2 ms (Tallinn probes of WaveCom and HostSlim to Hetzner HEL1; reverse direction not measurable, WaveCom's host does not answer ping) | +1.5 ms; operations take about 6 s and 24 s instead of 1.4 s and 6 s | Only cross-border pair near the 2 ms target. Neither country is in the Five, Nine or Fourteen Eyes groupings; both are EU and NATO members. Tallinn hardware, 10 Gbit/s ports and traffic pricing are unverified: third-party listings show WaveCom plans with 10 TB of traffic and older blade servers |
| 2 | Gcore (Luxembourg) + a Frankfurt provider | Luxembourg; UK, Netherlands or France | Luxembourg; Germany | 4.3 ms (Gcore Luxembourg to Leaseweb Frankfurt; one probe) | +3.8 ms; about 12 s and 49 s | Two states. Another Luxembourg probe (FranTech) took 13.3 ms to the same target, so the path depends heavily on the provider |
| 3 | OVHcloud Strasbourg + a Frankfurt provider | France; UK or Netherlands | France; Germany | 4.5 ms (OVH Strasbourg to Leaseweb Frankfurt; one probe) | +4.0 ms; about 13 s and 52 s | Two states, cheap unmetered traffic on the OVH side. France and Germany cooperate closely and both are in the Fourteen Eyes grouping |
| 4 | OVHcloud Gravelines + a London provider | France; US (Vultr) or UK | France; UK | 4.0 ms (OVH Gravelines to Vultr London; one probe) | +3.5 ms | Puts one node under the UK Investigatory Powers Act; not an improvement |
| 5 | A Zurich provider + a Frankfurt provider | Switzerland; UK, Netherlands or France | Switzerland; Germany | 5.8 ms (Exoscale and Init7 Zurich to Leaseweb Frankfurt; Init7 to Clouvider was 16.7 ms) | +5.3 ms; about 16 s and 67 s | Switzerland is outside the EU and the Eyes groupings |
| 6 | Amsterdam + Frankfurt | Netherlands or France; UK or Netherlands | Netherlands; Germany | 6.6 ms (Leaseweb to Leaseweb), 8.2 ms (Scaleway to Clouvider) | +6 ms; about 19 s and 76 s | Two states, both in the Fourteen Eyes grouping |
| 7 | Reykjavik + anywhere | Iceland | Iceland; other | 35.5 ms to London, 39.5 ms to Amsterdam | unusable for the computation link | Suitable only for a database node |
| — | Same metro, companies incorporated in different countries (pairs A, B, D, G) | two | one | 0.3–1.9 ms | none | The host country's courts and agencies can reach both machines, because the machine is where the data centre is. Separation of incorporation limits only company-level orders from a third country |

**Best pair when jurisdictional separation comes first:** Helsinki plus Tallinn, at about 2.1 ms, which is roughly 1.5 ms worse than the best same-metro pairs. It must be confirmed by renting in Tallinn (section 5). If Tallinn cannot supply the hardware, the fallback is a 4–6 ms pair into Frankfurt, which makes the long operation take about a minute.

### Cross-border candidates that did not work

| Candidate | Result | Detail |
|---|---|---|
| Vienna – Bratislava (about 60 km) | 5.3 ms at best; 12.8–23 ms on other paths | Bratislava probes (VNET, eServer, Castlegem) to DataPacket Vienna 5.3–5.5 ms; netcup, Anexia and Exoscale Vienna to a VNET Bratislava host 12.8–23.2 ms. The fibre distance would allow about 1 ms, but public routing between hosting networks does not deliver it. A leased wavelength could; not priced |
| Strasbourg – Kehl / Offenburg / Karlsruhe | 5.7–34 ms | Offenburg to OVH Strasbourg 7.1 ms; IONOS Karlsruhe 12.2 and 34.3 ms; Contabo Lauterbourg 5.7 ms; velia Strasbourg (a German company in a French building in the same city) 9.4 ms. Traffic hairpins through Frankfurt or Paris |
| Roubaix – Belgium | 10–19 ms | Brussels probes (M247, Datacamp, EDIS) to OVH Roubaix 10.2–11.8 ms; Kortrijk, 25 km away, 18.9 ms |
| Copenhagen – Malmö | 21 ms | Obehosting Malmö to DataPacket Copenhagen 20.8–21.2 ms. UpCloud Copenhagen to the same host was itself 9.8 ms, so the target is poorly placed and this result is weak. Bahnhof and GleSYS both list facilities in Malmö and Copenhagen (PeeringDB); untested |
| Falkenstein / Nuremberg – Czech Republic | 10.5–15.7 ms | Hetzner Nuremberg to DataPacket Prague 10.5 ms; Falkenstein 11.9 ms; Karlovy Vary to Falkenstein 15.7 ms |
| Basel – Strasbourg | 10.3 ms | Init7 Basel to OVH Strasbourg |
| Geneva – neighbouring France | not tested | No French hosting provider near Geneva found. Infomaniak Geneva to Frankfurt is 15.7 ms |
| Luxembourg – Strasbourg | 7.9 ms | FranTech Luxembourg to OVH Strasbourg |
| Singapore – Johor | minimum 1.9–2.5 ms, average 14–17 ms | Two Johor probes to Vultr Singapore; heavy jitter; no suitable bare-metal provider identified in Johor |
| Helsinki – Tallinn, other networks | 7.4–57 ms | Telia 7.4 ms, InfoNet 12.5 ms, Tele2 35 ms, xTom 55–57 ms. Only WaveCom and HostSlim had the short path |

## 3. Options that avoid the public internet

None of these was quoted for this report. Lead times are rules of thumb, not sourced.

| Option | What it is | Rough cost | Lead time | Notes |
|---|---|---|---|---|
| Hetzner colocation with a 10 Gbit/s uplink, next to netcup or another tenant | Own hardware in a Hetzner rack | Single 10 Gbit/s uplink €299 setup, €99/month, traffic €1.00/TB; redundant 2x10 Gbit/s €1,500 setup, €1,000/month. Rack rental and power are on a separate page not fetched. https://docs.hetzner.com/robot/colocation/pricing | weeks | Still one facility operator for both nodes |
| Two colocation contracts in one carrier-neutral building with a cross-connect | Own or rented hardware from two companies, joined by a fibre in the meet-me room | Equinix charges a one-time installation plus a monthly fee per cross-connect (https://docs.equinix.com/cross-connect/xc-pricing-billing-terms). A reseller lists about $142.50/month for a cross-connect within the Frankfurt Equinix campus (https://www.voxility.com/cross-connects/prices/Cross+Connect+from+Equinix+KleyerStrasse+FR5+Frankfurt). Colocation space and power not priced | cross-connect days to two weeks once both parties are in place; colocation contract and hardware 4–8 weeks | Gives the lowest and most stable latency (tens of microseconds) and no traffic charges. The building operator has physical access to both machines |
| Bare metal from two providers that both sell a cross-connect or private port in the same building | Rented servers, private fibre between them | By quote. Candidates by facility listing: Iron Mountain AMS-1 (Scaleway, Vultr, Latitude.sh, Hivelocity, NovoServe, Servers.com), Equinix Frankfurt (Clouvider, FDCservers, Servers.com), Digital Realty Frankfurt (Vultr, Hivelocity, Worldstream) | weeks; depends on both sales teams | I found no public price list from any of these for a customer cross-connect on a rented server. Ask each |
| Interconnect between two hyperscale clouds | For example AWS Direct Connect on one side and another cloud's interconnect on the other, joined in a shared facility | AWS dedicated 10 Gbit/s port $2.25/hour (about $1,640/month) plus data transfer out; a third-party figure of $0.02/GB gives $400 for 20 TB (https://aws.amazon.com/directconnect/pricing/). The other cloud's port and egress add a similar amount | days to weeks | Much dearer than bare metal, both companies are US-based, and round-trip time inside clouds is typically no better than the bare-metal pairs measured here |
| Leased wavelength between two cities | A dedicated optical circuit, for example Vienna–Bratislava or Helsinki–Tallinn | By quote; typically four figures per month for 10 Gbit/s | 1–3 months | The only way to make a cross-border pair reach its physical limit (about 1 ms per 100 km of fibre) |

## 4. Candidates for the five database nodes

Requirement: 4 cores, 16 GB, small traffic, no provider hosting three, tens of milliseconds acceptable. The right set depends on the computation metro; the list is ordered for a Frankfurt, Amsterdam or Helsinki choice. Prices marked "check" could not be fetched today.

| Provider | Company and parent | Locations near the candidate metros | Product and price | Independence notes |
|---|---|---|---|---|
| UpCloud | UpCloud Oy, Finland | Helsinki, Frankfurt, Amsterdam, Copenhagen, Stockholm (PeeringDB) | Cloud server; a 4-CPU 16 GB "Starter" plan carries a 2.5 TB fair-transfer allowance (https://upcloud.com/docs/products/networking/network-transfer/); price check | Independent; Frankfurt site is in Digital Realty |
| Exoscale | Akenes SA, Switzerland; owned by A1 Telekom Austria group | Zurich, Geneva, Frankfurt, Vienna, Munich | Cloud instance; third-party sources say about 1 TiB egress included per instance; price check | Swiss company; choose the Zurich or Geneva zone for Swiss jurisdiction |
| Infomaniak | Infomaniak Network SA, Switzerland | Geneva area | Public cloud; "bandwidth is free" (https://www.infomaniak.com/en/hosting/public-cloud/prices); price check | 15.7 ms to Frankfurt measured |
| OVHcloud | OVH Groupe SA, France | Limburg, Strasbourg, Gravelines, Roubaix, London, Warsaw | VPS or small dedicated server; unmetered; price check | Do not count as independent of the computation node if OVH hosts one |
| Hetzner | Hetzner Online GmbH, Germany | Falkenstein, Nuremberg, Helsinki | Cloud or small dedicated server; EU cloud plans include about 20 TB; price check after the June 2026 increase | Same caveat if Hetzner hosts a computation node |
| netcup | netcup GmbH, Germany; owned by Anexia, Austria | Nuremberg, Vienna | RS 2000 G12.5, 8 dedicated cores, 16 GB, €40.70/month (https://www.netcup.com/en/server/root-server) | Nuremberg site is inside Hetzner's building; use Vienna if Hetzner is also used. Do not count netcup and Anexia as two providers |
| Scaleway | Scaleway SAS, France; Iliad group | Paris, Amsterdam, Warsaw | Instance; price check | |
| Leaseweb | Leaseweb Global B.V., Netherlands | Amsterdam, Frankfurt, London | Cloud or small dedicated server; price check | |
| GleSYS or Bahnhof | Swedish companies | Stockholm, Falkenberg, Malmö; GleSYS also Finland | Cloud server; price check | Swedish jurisdiction; Sweden permits signals intelligence on cross-border cables |
| FlokiNET or 1984 | Icelandic companies | Reykjavik; FlokiNET also Helsinki, Romania, Netherlands | VPS; price check | 35–40 ms to London and Amsterdam measured; adds a jurisdiction outside the EU |
| Vultr, DigitalOcean, Akamai (Linode) | US companies | Frankfurt, Amsterdam, Paris, London | Cloud instances; price check | All reachable under US law wherever the server is; use at most one, and preferably none |

A spread that puts jurisdiction first, with no state hosting more than two and no US company: UpCloud (Finland, Helsinki), Exoscale or Infomaniak (Switzerland), OVHcloud (France, Strasbourg or Gravelines), Hetzner (Germany, Falkenstein), GleSYS or Bahnhof (Sweden). If OVHcloud or Hetzner already hosts a computation node, replace it with Leaseweb (Netherlands) or FlokiNET (Iceland).

## 5. What could not be verified, and how to settle it

### Not verified

- **Latency to an actual rented server.** Every figure is to a provider's public test host. The server you rent may sit in a different hall or a different building of the same provider.
- **Stability over time.** One evening snapshot, 8 packets per probe. No information on daily variation, loss under load, or route changes.
- **Both directions.** Several pairs were measured one way only. Routes are often asymmetric: OVH to Clouvider Frankfurt took 9.3 ms while every other Frankfurt path from OVH took 1.4–1.9 ms.
- **Throughput.** No bandwidth test was possible. Whether a "10 Gbit/s" port sustains multi-gigabit flow to the other provider is unknown.
- **Buildings.** PeeringDB facility records show where a network has presence, which is often a router and not the server hall. Leaseweb's and DataPacket's ASNs had no facility records in the data.
- **Prices** for Leaseweb, Scaleway, Vultr, UpCloud, FDCservers, WaveCom and all database-node products, for the reasons given at the top.
- **Overage rates** at Clouvider and Hetzner's US cloud.
- **netcup's traffic terms**, known only from a forum quotation.
- **Whether any Tallinn provider can supply a 12-core, 64 GB machine with a 10 Gbit/s port** and what the traffic costs.
- **Any provider's behaviour towards informal requests** (section 6).

### Measurement plan

For each candidate pair, rent the smallest hourly or monthly product in the exact data centre at both providers. Hourly cloud instances exist at Scaleway, Vultr, Hetzner (cloud), UpCloud, OVHcloud and Exoscale; Clouvider, Leaseweb, netcup, WaveCom and Hetzner dedicated servers are monthly, so budget one month for those. Order of testing: pair A and pair B first, then Helsinki–Tallinn, then pair D.

1. **Bring up WireGuard between the two machines** with the MTU set to 1420, and run every test both inside the tunnel and outside it.
2. **Latency.** `ping -i 0.2 -c 3000` in both directions, and `mtr -rwzc 300` in both directions to record the path and the networks crossed. Repeat at four times of day: about 03:00, 10:00, 15:00 and 21:00 local time, over at least three days including a weekend day.
3. **Request-response rate.** The protocol's cost is sequential round trips, so measure that directly: `netperf -t TCP_RR` or `sockperf ping-pong` inside the tunnel for 60 seconds, with small and with 16 KB messages. Convert to round trips per second.
4. **Throughput.** `iperf3 -P 8 -t 60` in both directions, then a 30-minute run to expose throttling, inside and outside the tunnel. Watch CPU use of WireGuard at multi-gigabit rates.
5. **Volume test.** Push 1 TB each way in one day and check the provider's traffic counter, the invoice preview, and whether any abuse or fair-use notice arrives.
6. **The real workload.** Run both kinds of operation ten times each and record wall-clock time.

A pair qualifies if, inside WireGuard, at every time of day:

- median round trip is at most 1.0 ms and the 99th percentile at most 2.0 ms (relax to 2.5 ms median only for a pair chosen for jurisdictional separation);
- packet loss is below 0.01 %;
- the route in both directions stays inside the metro, with no detour through another city;
- sustained throughput is at least 3 Gbit/s each way on ports sold as 10 Gbit/s, with no drop during the 30-minute run;
- the 1 TB test produces no notice and no unexpected charge.

## 6. Risks

### Traffic and commercial terms

- **"Unmetered" has limits.** OVHcloud's bandwidth page says service may continue with reduced quality if usage exceeds limits. netcup reportedly limits a port to 200 Mbit/s after 120 TB with sustained use above 1 Gbit/s. UpCloud throttles to 100 Mbit/s past its fair-transfer limit. Clouvider's "up to 10 Gbit/s unmetered" wording sits beside a 50 or 100 TB allowance; ask which governs.
- **Hetzner's 10 Gbit/s uplink ends the unlimited-traffic policy** for that server and disables the Robot firewall.
- **Counting rules differ.** Hetzner counts outbound only. Others may count the larger of in and out, or the sum. Symmetric traffic doubles the bill under a sum rule.
- **Price changes.** Hetzner raised cloud prices sharply in June 2026 and its dedicated prices are higher than older listings show. Do not rely on any figure here that is older than this report.
- **Sustained high-volume encrypted traffic between two fixed addresses** resembles a tunnel or a relay. Tell each provider's support in advance what it is; some providers' acceptable-use terms restrict VPN endpoints or proxies. I did not read each provider's terms in full, so check them before ordering.
- **Account verification.** Hetzner, netcup, OVHcloud and Scaleway commonly ask for identity documents and may hold or cancel new accounts; netcup and Hetzner are known for cancelling accounts during verification. Allow a week and open accounts early.
- **Stock.** Large configurations (netcup RS 16000, some Clouvider models) are "on request".

### Shared infrastructure that looks independent

- netcup in Nuremberg is inside Hetzner's facility. netcup and Anexia are one group.
- Many providers in one metro are tenants of the same landlord (Equinix, Digital Realty, Iron Mountain). That is what makes sub-millisecond paths possible, and it means one facility operator has physical access to both machines.
- Contabo is German but owned by a US private-equity firm; the same kind of ownership question applies to any provider and changes over time.
- Clouvider, Vultr, HostHatch and similar providers rent space from others in every location.

### Jurisdiction, by provider

"Nothing found" means my searches today returned no transparency report or warrant canary; it does not mean none exists.

| Provider | Company and ultimate parent | Data centres considered | Legal regimes that can reach it | Public record |
|---|---|---|---|---|
| Hetzner | Hetzner Online GmbH, Germany; privately held; Finnish and US subsidiaries | Germany, Finland, United States | German criminal procedure and intelligence law; Finnish law for Helsinki; US law for Ashburn and, through the US subsidiary, possibly a route for US orders | No transparency report found. In 2023 traffic to a customer's server at Hetzner and at Linode in Germany was intercepted by rerouting inside the providers' networks; the researchers concluded it was probably lawful interception; neither provider commented publicly (https://therecord.media/jabber-ru-alleged-government-wiretap-expired-tls-certificate) |
| netcup | netcup GmbH, Germany; Anexia, Austria | Germany (in Hetzner's facility), Austria | German law; Austrian law for the parent and the Vienna site | Nothing found |
| OVHcloud | OVH Groupe SA, France; listed in Paris; separate US and Canadian subsidiaries | France, Germany, UK, Poland, United States, Canada | French law everywhere it operates as the parent; local law per site; its US FAQ says the government needs a subpoena, court order or warrant and that customers are notified unless prohibited (https://us.ovhcloud.com/resources/faqs/legal-law-enforcement) | In September 2025 an Ontario court upheld an order requiring OVH to produce data held in Europe through its Canadian subsidiary; OVH is contesting it, citing the French blocking statute (https://www.theregister.com/2025/11/27/canada_court_ovh). This shows a subsidiary can be used as a lever across borders |
| Scaleway | Scaleway SAS, France; Iliad group | France, Netherlands, Poland | French law; Dutch law for Amsterdam | Nothing found |
| Leaseweb | Leaseweb Global B.V., Netherlands; national sales entities in Germany, UK, US | Netherlands, Germany, UK, United States | Dutch law for the group; local law per entity; US law for the US entity | Published the first hosting-provider transparency report in 2013, covering government requests for customer information and forensic images (https://www.bitsoffreedom.nl/2013/04/16/dutch-provider-first-to-publish-transparency-report); a 2023 report exists (https://leaseweb.com/sites/default/files/Legal/Leaseweb-transparency-reoprt-2023-updated.pdf) |
| Clouvider | Clouvider Limited, United Kingdom | Germany, Netherlands, UK, United States | UK Investigatory Powers Act for the company; local law per site | Nothing found |
| Vultr | The Constant Company, United States | worldwide | US CLOUD Act and FISA section 702 wherever the server is; local law per site | Nothing found today |
| UpCloud | UpCloud Oy, Finland | Finland, Germany, Netherlands, others | Finnish law; local law per site | Nothing found |
| Exoscale | Akenes SA, Switzerland; A1 Telekom Austria group | Switzerland, Germany, Austria | Swiss law; Austrian parent; local law per site | Nothing found |
| Infomaniak | Infomaniak Network SA, Switzerland | Switzerland | Swiss surveillance law | Nothing found today |
| WaveCom | WaveCom AS, Estonia | Estonia | Estonian law | Nothing found |
| Worldstream | Worldstream B.V., Netherlands | Netherlands, Germany | Dutch law | Nothing found |
| FDCservers, Hivelocity, ReliableSite, HostHatch, DigitalOcean, Akamai | United States | worldwide | US CLOUD Act and FISA section 702 | DigitalOcean publishes a transparency report (https://www.digitalocean.com/legal/transparency-report); others nothing found |
| Gcore | G-Core Labs S.A., Luxembourg | Luxembourg, many others | Luxembourg law; local law per site | Nothing found |

Regimes to keep in mind (general knowledge, not re-verified today):

- **United States.** The CLOUD Act lets US authorities order a provider subject to US jurisdiction to produce data it controls anywhere in the world; FISA section 702 covers US electronic communication service providers. A European company with a US subsidiary is not automatically exempt, as the OVH Canada case illustrates for another country.
- **United Kingdom.** The Investigatory Powers Act allows technical capability notices served in secret on operators.
- **Germany, France, Netherlands, Sweden, Finland, Switzerland.** Each permits targeted interception by court or ministerial order, and each has a law permitting intelligence collection on international cable traffic. That matters little here because the link is encrypted; what matters is an order to the host to image or tap a machine.
- **Alliances.** Five Eyes: US, UK, Canada, Australia, New Zealand. The wider groupings usually described add Denmark, France, the Netherlands and Norway, then Germany, Belgium, Italy, Spain and Sweden. Finland, Estonia, Austria, Switzerland, Luxembourg, Iceland, the Czech Republic and Slovakia are outside those lists, though all cooperate with partners in other forms.

### Limits of this assessment

- **Public information cannot show that a provider refuses informal requests.** A transparency report counts formal orders the provider chose to report. The absence of a report, or the presence of one, says nothing about quiet cooperation, and gag orders prevent disclosure of the cases that matter most.
- **Physical access defeats legal distinctions.** Whoever operates the building or the server can copy a disk, read memory through a management controller or a bus, or tap the network port, whether ordered to or not. In a same-metro pair this is one landlord for both nodes.
- **Two companies in one country are one legal target.** A single court or agency can serve both. Different incorporation helps only against orders from a third state addressed to the company.
- **Corporate structure changes.** Acquisitions (netcup by Anexia, Contabo by a US fund) alter the picture after the contract is signed.

### Technical measures that reduce reliance on the provider

| Measure | What it protects against | What it does not | Cost |
|---|---|---|---|
| WireGuard between nodes (already planned) | Reading or altering traffic on the path, including cross-border cable collection | Anything on the machine itself | none |
| Full-disk encryption with the key entered remotely at boot (for example over an SSH session in the initial ramdisk) or released by a remote key server | Disk imaging of a powered-off or seized machine; disks reused after cancellation | Memory capture from a running machine; a tampered boot environment that records the key | Free; an unattended reboot needs the key server or a person |
| Measured boot with a TPM and remote attestation before the key is released | A modified boot chain or kernel | A physical attack on a running machine; trust in the TPM and firmware vendor | Engineering time; hardware with a TPM, which most current servers have |
| Memory encryption and confidential-computing features (AMD SEV-SNP, Intel TDX) on hardware that supports them | A host operator or hypervisor reading memory, on the netcup-style virtual server in particular | Side channels and firmware flaws; needs provider support, which most bare-metal sellers do not advertise | Limits the choice of hardware and provider |
| Owning the hardware in colocation, in a locked rack or cage with tamper-evident seals and chassis-intrusion alarms | Silent access by the hosting company's staff; removes the provider's management-controller access | A facility operator acting under an order; needs remote hands you trust | Purchase of two servers, colocation fees (not priced here; uplink figures in section 3), travel for installation, 4–8 weeks |
| Disabling or isolating the management controller, and no provider rescue-system access | Remote console access by the provider | Physical access | Free; makes recovery harder |
| Splitting the two nodes across two states | A single state compelling both | Cooperation between states; costs at least 1.5 ms per round trip on the evidence here | Latency |

The protocol's own guarantee is that one honest node suffices. The measures above are about making it hard for one actor to hold both nodes, and for that purpose the order of value is: two different facility operators, then two different states, then owned hardware.

## Appendix A — Raw measurements

Source: Globalping public probes, 11 Nov 2026, about 21:50–22:20 UTC, ICMP, 8 packets. Each line gives the label, the probe's network and city, the target host and address, minimum/average/maximum round trip in milliseconds, loss in percent, and the measurement ID, retrievable for a limited time at `https://api.globalping.io/v1/measurements/<id>`. Label prefixes: metro code for same-metro tests, XB for cross-border neighbours, XJ for cross-jurisdiction longer paths. OVH probes labelled Frankfurt are in OVH's German data centre at Limburg. Hostnames containing "datapacket" are served by a content network and may not be in the named city.

```
NBG netcup->Hetzner | src netcup AS197540 Nuremberg,DE -> nbg1-speed.hetzner.com (78.47.119.196) | min 0.815 avg 0.859 max 0.913 loss 0 | id 2suBXVR3My2zLGpFZ00021UEw
NBG netcup->Hetzner | src netcup AS197540 Nuremberg,DE -> nbg1-speed.hetzner.com (78.47.119.196) | min 0.683 avg 0.783 max 0.959 loss 0 | id 2suBXVR3My2zLGpFZ00021UEw
NBG netcup->Hetzner | src netcup AS197540 Nuremberg,DE -> nbg1-speed.hetzner.com (78.47.119.196) | min 0.402 avg 0.449 max 0.534 loss 0 | id 2suBXVR3My2zLGpFZ00021UEw
NBG netcup->Hetzner FSN | src netcup AS197540 Nuremberg,DE -> fsn1-speed.hetzner.com (78.46.170.2) | min 3.023 avg 3.1 max 3.241 loss 0 | id 2OhMs8FNWqUXIK4YX00021UEw
NBG Contabo->Hetzner | src Contabo AS51167 Nuremberg,DE -> nbg1-speed.hetzner.com (78.47.119.196) | min 9.333 avg 9.958 max 11.498 loss 0 | id 2zAU7Xyu5XBsGDH6n00021UEx
FRA OVH->Leaseweb | src OVH AS16276 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.601 avg 1.677 max 1.719 loss 0 | id 2QsLMYyUHpUnaGCmQ00021UEx
FRA OVH->Leaseweb | src OVH AS16276 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.841 avg 1.872 max 1.926 loss 0 | id 2QsLMYyUHpUnaGCmQ00021UEx
FRA OVH(Limburg)->Leaseweb | src OVH AS16276 Limburg an der Lahn,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.626 avg 1.653 max 1.69 loss 0 | id 2jt6CEdpvP0pX1oKl00021UEx
FRA OVH->Vultr | src OVH AS16276 Frankfurt,DE -> fra-de-ping.vultr.com (108.61.210.117) | min 1.614 avg 1.673 max 1.744 loss 0 | id 2nFCvuCXrw3IhCWlu00021UEx
FRA OVH->Vultr | src OVH AS16276 Frankfurt,DE -> fra-de-ping.vultr.com (108.61.210.117) | min 1.471 avg 1.542 max 1.591 loss 0 | id 2nFCvuCXrw3IhCWlu00021UEx
FRA OVH->Clouvider | src OVH AS16276 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 9.355 avg 9.497 max 10.002 loss 0 | id 2isfz2fb1tRa6c1by00021UEx
FRA OVH->Clouvider | src OVH AS16276 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 9.284 avg 9.319 max 9.356 loss 0 | id 2isfz2fb1tRa6c1by00021UEx
FRA OVH->Datapacket | src OVH AS16276 Frankfurt,DE -> fra.download.datapacket.com (195.181.175.41) | min 2.044 avg 2.6 max 3.134 loss 0 | id 2kHyxCEViET7giVVj00021UEx
FRA OVH->Datapacket | src OVH AS16276 Frankfurt,DE -> fra.download.datapacket.com (89.222.125.2) | min 2.253 avg 2.369 max 2.527 loss 0 | id 2kHyxCEViET7giVVj00021UEx
FRA OVH->FDC | src OVH AS16276 Frankfurt,DE -> lg-fra.fdcservers.net (50.7.50.14) | min 1.421 avg 1.488 max 1.533 loss 0 | id 2gm3ijUSBRtON8Tf100021UEx
FRA OVH->FDC | src OVH AS16276 Frankfurt,DE -> lg-fra.fdcservers.net (50.7.50.14) | min 1.411 avg 1.624 max 1.984 loss 0 | id 2gm3ijUSBRtON8Tf100021UEx
FRA OVH->Linode | src OVH AS16276 Frankfurt,DE -> speedtest.frankfurt.linode.com (139.162.130.8) | min None avg None max None loss 100 | id 2njb1cee3TD9xFBQp00021UEx
FRA Leaseweb->Vultr | src LeaseWeb AS28753 Frankfurt,DE -> fra-de-ping.vultr.com (108.61.210.117) | min 0.813 avg 3.158 max 19.241 loss 0 | id 2AQpvzk2ah1qzmG6W00021UEx
FRA Leaseweb->Vultr | src LeaseWeb AS28753 Frankfurt,DE -> fra-de-ping.vultr.com (108.61.210.117) | min 0.904 avg 0.947 max 1.088 loss 0 | id 2AQpvzk2ah1qzmG6W00021UEx
FRA Leaseweb->Clouvider | src LeaseWeb AS28753 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.632 avg 0.687 max 0.727 loss 0 | id 2D4GnqbkX5IwDufI700021UEx
FRA Leaseweb->Clouvider | src LeaseWeb AS28753 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.701 avg 0.88 max 1.183 loss 0 | id 2D4GnqbkX5IwDufI700021UEx
FRA Leaseweb->Datapacket | src LeaseWeb AS28753 Frankfurt,DE -> fra.download.datapacket.com (89.222.125.2) | min 1.482 avg 1.606 max 2.111 loss 0 | id 2cK5u8gd3rZXfe2Jx00021UEx
FRA Leaseweb->Datapacket | src LeaseWeb AS28753 Frankfurt,DE -> fra.download.datapacket.com (89.222.125.5) | min 1.512 avg 1.617 max 1.76 loss 0 | id 2cK5u8gd3rZXfe2Jx00021UEx
FRA Leaseweb->FDC | src LeaseWeb AS28753 Frankfurt,DE -> lg-fra.fdcservers.net (50.7.50.14) | min 0.824 avg 0.898 max 1.009 loss 0 | id 2f0CvE9DLBQDfs54L00021UEx
FRA Leaseweb->FDC | src LeaseWeb AS28753 Frankfurt,DE -> lg-fra.fdcservers.net (50.7.50.14) | min 0.839 avg 0.911 max 1.046 loss 0 | id 2f0CvE9DLBQDfs54L00021UEx
FRA Clouvider->Leaseweb | src Clouvider AS62240 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 0.624 avg 0.678 max 0.812 loss 0 | id 2EIZ90vYKrVGnNs2900021UEx
FRA Clouvider->Vultr | src Clouvider AS62240 Frankfurt,DE -> fra-de-ping.vultr.com (108.61.210.117) | min 0.647 avg 0.689 max 0.799 loss 0 | id 2EmCaYBaqMuWHy1dg00021UEx
FRA Clouvider->Datapacket | src Clouvider AS62240 Frankfurt,DE -> fra.download.datapacket.com (89.222.125.5) | min 1.378 avg 1.462 max 1.556 loss 0 | id 2BdrkDzZDBEjAtquy00021UEx
FRA Clouvider->FDC | src Clouvider AS62240 Frankfurt,DE -> lg-fra.fdcservers.net (50.7.50.14) | min 0.492 avg 0.576 max 0.696 loss 0 | id 2eOxCtzonzW20Mcx800021UEx
FRA Vultr->Leaseweb | src The Constant Company AS20473 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 0.937 avg 1.241 max 1.41 loss 0 | id 25mtOL4wF6C8rxotS00021UEx
FRA Vultr->Leaseweb | src The Constant Company AS20473 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.095 avg 1.263 max 1.416 loss 0 | id 25mtOL4wF6C8rxotS00021UEx
FRA Vultr->Clouvider | src The Constant Company AS20473 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.552 avg 0.591 max 0.628 loss 0 | id 2aDsAhFYtDMvzBKdW00021UEx
FRA Vultr->Clouvider | src The Constant Company AS20473 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.667 avg 0.73 max 0.792 loss 0 | id 2aDsAhFYtDMvzBKdW00021UEx
FRA Hivelocity->Leaseweb | src Hivelocity AS29802 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.229 avg 4.261 max 21.737 loss 0 | id 2oJ7YlCIuUHKLWMwh00021UEx
FRA Hivelocity->Vultr | src Hivelocity AS29802 Frankfurt,DE -> fra-de-ping.vultr.com (108.61.210.117) | min 0.473 avg 0.526 max 0.654 loss 0 | id 2wYilOyY7M6zHQd7f00021UEx
FRA Hivelocity->Clouvider | src Hivelocity AS29802 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 13.535 avg 13.791 max 15.005 loss 0 | id 2lTQRZiLRbrdkJs1Y00021UEx
FRA IONOS->Leaseweb | src IONOS AS8560 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 6.793 avg 6.984 max 7.124 loss 0 | id 2eV6eB2PiGfHSI3YT00021UEx
FRA IONOS->Clouvider | src IONOS AS8560 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 2.788 avg 2.858 max 2.914 loss 0 | id 2TI3edKb2kbHUCiNE00021UEx
FRA UpCloud->Leaseweb | src UpCloud AS202053 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 6.876 avg 6.985 max 7.171 loss 0 | id 2iaJxldu9Isw2XWAC00021UEx
FRA Exoscale->Leaseweb | src Akenes AS61098 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 0.892 avg 1.018 max 1.098 loss 0 | id 2Zt5ORN2GbfYyOySE00021UEx
FRA Exoscale->Clouvider | src Akenes AS61098 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.51 avg 0.545 max 0.567 loss 0 | id 2FluLiQ37vIWfhL3700021UEx
FRA Hetzner FSN->Leaseweb FRA | src Hetzner Online AS24940 Falkenstein,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 5.338 avg 5.568 max 5.788 loss 12.5 | id 2VhLIfmnICEJHpg8p00021UEx
FRA Hetzner NBG->Leaseweb FRA | src Hetzner Online AS24940 Nuremberg,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 4.012 avg 4.7 max 8.903 loss 0 | id 2cOyrMTWUZZmx3N1G00021UEx
AMS Leaseweb->Vultr | src LeaseWeb AS60781 Amsterdam,NL -> ams-nl-ping.vultr.com (108.61.198.102) | min 0.765 avg 0.807 max 0.881 loss 0 | id 2oiXfn9pBUC3yipiX00021UEx
AMS Leaseweb->Vultr | src LeaseWeb AS60781 Amsterdam,NL -> ams-nl-ping.vultr.com (108.61.198.102) | min 0.298 avg 0.465 max 0.609 loss 0 | id 2oiXfn9pBUC3yipiX00021UEx
AMS Leaseweb->Clouvider | src LeaseWeb AS60781 Amsterdam,NL -> ams.speedtest.clouvider.net (194.127.172.176) | min 0.94 avg 1.025 max 1.127 loss 0 | id 2sFl58zxZQW8yiHF800021UEx
AMS Leaseweb->Clouvider | src LeaseWeb AS60781 Amsterdam,NL -> ams.speedtest.clouvider.net (194.127.172.176) | min 0.729 avg 0.806 max 0.909 loss 0 | id 2sFl58zxZQW8yiHF800021UEx
AMS Leaseweb->Datapacket | src LeaseWeb AS60781 Amsterdam,NL -> ams.download.datapacket.com (195.181.172.3) | min 1.728 avg 1.757 max 1.778 loss 0 | id 2v4xxL2UkEDnjQ03400021UEx
AMS Leaseweb->Datapacket | src LeaseWeb AS60781 Amsterdam,NL -> ams.download.datapacket.com (195.181.172.2) | min 1.671 avg 2.182 max 4.449 loss 0 | id 2v4xxL2UkEDnjQ03400021UEx
AMS Leaseweb->Worldstream | src LeaseWeb AS60781 Amsterdam,NL -> speedtest.worldstream.nl (185.182.195.78) | min 1.661 avg 2.052 max 2.412 loss 0 | id 2F0GFReejJBT5O9vE00021UEx
AMS Leaseweb->Worldstream | src LeaseWeb AS60781 Amsterdam,NL -> speedtest.worldstream.nl (185.182.195.78) | min 1.481 avg 1.881 max 2.444 loss 0 | id 2F0GFReejJBT5O9vE00021UEx
AMS Leaseweb->Scaleway | src LeaseWeb AS60781 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 0.827 avg 0.88 max 0.968 loss 0 | id 2E5nX3TjThqjxnszO00021UEx
AMS Leaseweb->Scaleway | src LeaseWeb AS60781 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 0.426 avg 0.462 max 0.48 loss 0 | id 2E5nX3TjThqjxnszO00021UEx
AMS Scaleway->Leaseweb | src SCALEWAY AS12876 Amsterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 0.771 avg 0.883 max 1.345 loss 0 | id 24N6sY3BjglET0BHR00021UEx
AMS Scaleway->Leaseweb | src SCALEWAY AS12876 Amsterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 1.043 avg 1.136 max 1.305 loss 0 | id 24N6sY3BjglET0BHR00021UEx
AMS Scaleway->Vultr | src SCALEWAY AS12876 Amsterdam,NL -> ams-nl-ping.vultr.com (108.61.198.102) | min 0.588 avg 0.798 max 1.434 loss 0 | id 2avrl2QYxFksP3OMq00021UEx
AMS Scaleway->Vultr | src SCALEWAY AS12876 Amsterdam,NL -> ams-nl-ping.vultr.com (108.61.198.102) | min 1.255 avg 1.588 max 2.156 loss 0 | id 2avrl2QYxFksP3OMq00021UEx
AMS Scaleway->Clouvider | src SCALEWAY AS12876 Amsterdam,NL -> ams.speedtest.clouvider.net (194.127.172.176) | min 1.076 avg 1.284 max 1.547 loss 0 | id 2EJHJtHbSDFMCE5OQ00021UEx
AMS Scaleway->Clouvider | src SCALEWAY AS12876 Amsterdam,NL -> ams.speedtest.clouvider.net (194.127.172.176) | min 1.126 avg 1.264 max 1.332 loss 0 | id 2EJHJtHbSDFMCE5OQ00021UEx
AMS Scaleway->Worldstream | src SCALEWAY AS12876 Amsterdam,NL -> speedtest.worldstream.nl (185.182.195.78) | min 1.781 avg 1.887 max 2.018 loss 0 | id 2TKkWrjSDxjCtpijy00021UEx
AMS Scaleway->Worldstream | src SCALEWAY AS12876 Amsterdam,NL -> speedtest.worldstream.nl (185.182.195.78) | min 1.736 avg 2.103 max 2.555 loss 0 | id 2TKkWrjSDxjCtpijy00021UEx
AMS Scaleway->Datapacket | src SCALEWAY AS12876 Amsterdam,NL -> ams.download.datapacket.com (195.181.172.2) | min 10.053 avg 10.145 max 10.215 loss 0 | id 2ie9SZdyapZdEfN9q00021UEx
AMS Worldstream->Leaseweb | src WorldStream AS49981 Rotterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 2.397 avg 2.672 max 2.858 loss 0 | id 25ziaavIifbqCt4Rk00021UEx
AMS Worldstream->Leaseweb | src WorldStream AS49981 Rotterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 1.446 avg 1.488 max 1.594 loss 0 | id 25ziaavIifbqCt4Rk00021UEx
AMS Worldstream->Scaleway | src WorldStream AS49981 Rotterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 1.419 avg 1.423 max 1.428 loss 0 | id 2Sx1zluA8VQfFEgoI00021UEx
AMS Worldstream->Scaleway | src WorldStream AS49981 Rotterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 1.418 avg 1.431 max 1.444 loss 0 | id 2Sx1zluA8VQfFEgoI00021UEx
AMS Worldstream->Clouvider | src WorldStream AS49981 Rotterdam,NL -> ams.speedtest.clouvider.net (194.127.172.176) | min 2.666 avg 2.842 max 3.005 loss 0 | id 2J5L9uniqUJNKVPNR00021UEx
AMS Servers.com->Leaseweb | src Servers.com AS7979 Amsterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 1.636 avg 1.688 max 1.823 loss 0 | id 2iguqlJC6NWnEPMfE00021UEx
AMS Servers.com->Scaleway | src Servers.com AS7979 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 1.609 avg 1.627 max 1.643 loss 0 | id 2zJWu4TYEmwbXa5oZ00021UEx
AMS Servers.com->Vultr | src Servers.com AS7979 Amsterdam,NL -> ams-nl-ping.vultr.com (108.61.198.102) | min 1.368 avg 1.388 max 1.42 loss 0 | id 2RQ1lJQ67pqv4KtB300021UEx
AMS Hivelocity->Scaleway | src Hivelocity AS29802 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 1.372 avg 1.55 max 2.237 loss 0 | id 2nSIwAA6ni6vc0Z3F00021UEx
AMS Hivelocity->Leaseweb | src Hivelocity AS29802 Amsterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 0.949 avg 1.049 max 1.206 loss 0 | id 2KK4pYtzNYj4WC9b000021UEx
AMS Hivelocity->Vultr | src Hivelocity AS29802 Amsterdam,NL -> ams-nl-ping.vultr.com (108.61.198.102) | min 1.065 avg 1.181 max 1.612 loss 0 | id 23StKieB4ycbaht6A00021UEx
AMS Vultr->Scaleway | src The Constant Company AS20473 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 0.312 avg 0.389 max 0.565 loss 0 | id 2ZJwRBjOGAmt4ZUH200021UEx
AMS Vultr->Scaleway | src The Constant Company AS20473 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 0.926 avg 0.982 max 1.033 loss 0 | id 2ZJwRBjOGAmt4ZUH200021UEx
AMS Vultr->Leaseweb | src The Constant Company AS20473 Amsterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 0.8 avg 0.849 max 0.898 loss 0 | id 2BFZD0nA7y22D7hZS00021UEx
AMS Vultr->Leaseweb | src The Constant Company AS20473 Amsterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 0.775 avg 0.815 max 0.847 loss 0 | id 2BFZD0nA7y22D7hZS00021UEx
AMS OVH->Leaseweb | src OVH AS16276 Amsterdam,NL -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 1.041 avg 1.12 max 1.387 loss 0 | id 2yZJI7e4lt0LQ5loW00021UEx
PAR Scaleway->Vultr | src SCALEWAY AS12876 Paris,FR -> par-fr-ping.vultr.com (108.61.209.127) | min 1.16 avg 1.238 max 1.295 loss 0 | id 2u0gm4dKhZAtWpEPt00021UEx
PAR Scaleway->Vultr | src SCALEWAY AS12876 Paris,FR -> par-fr-ping.vultr.com (108.61.209.127) | min 1.328 avg 1.38 max 1.419 loss 0 | id 2u0gm4dKhZAtWpEPt00021UEx
PAR Scaleway->Datapacket | src SCALEWAY AS12876 Paris,FR -> par.download.datapacket.com (185.93.2.9) | min 0.793 avg 0.925 max 1.116 loss 0 | id 2MIOoDUKipY2AV3zv00021UEx
PAR Scaleway->Datapacket | src SCALEWAY AS12876 Paris,FR -> par.download.datapacket.com (79.127.178.167) | min 1.58 avg 2.012 max 2.536 loss 0 | id 2MIOoDUKipY2AV3zv00021UEx
PAR Scaleway->OVH RBX | src SCALEWAY AS12876 Paris,FR -> rbx.proof.ovh.net (141.95.207.211) | min 4.714 avg 4.793 max 4.973 loss 0 | id 2It9j2BYMGH9JAH4M00021UEx
PAR Scaleway->OVH RBX | src SCALEWAY AS12876 Paris,FR -> rbx.proof.ovh.net (141.95.207.211) | min 4.927 avg 4.963 max 5.02 loss 0 | id 2It9j2BYMGH9JAH4M00021UEx
PAR Scaleway->OVH GRA | src SCALEWAY AS12876 Paris,FR -> gra.proof.ovh.net (141.94.30.145) | min 6.443 avg 7.335 max 10.685 loss 0 | id 23g6wieCIT3TPe9i800021UEx
PAR Vultr->Scaleway | src The Constant Company AS20473 Paris,FR -> ping.online.net (51.158.1.21) | min 0.708 avg 0.781 max 0.864 loss 0 | id 2Vx2q7yAjtPQXhWHS00021UEx
PAR Vultr->Scaleway | src The Constant Company AS20473 Paris,FR -> ping.online.net (51.158.1.21) | min 0.656 avg 0.697 max 0.721 loss 0 | id 2Vx2q7yAjtPQXhWHS00021UEx
PAR OVH RBX->Scaleway | src OVH AS16276 Roubaix,FR -> ping.online.net (51.158.1.21) | min 6.281 avg 6.341 max 6.358 loss 0 | id 2SFQxe8Pcu7TF15KT00021UEx
PAR OVH RBX->Scaleway | src OVH AS16276 Roubaix,FR -> ping.online.net (51.158.1.21) | min 5.392 avg 5.417 max 5.503 loss 0 | id 2SFQxe8Pcu7TF15KT00021UEx
PAR Datacamp->Scaleway | src Datacamp AS60068 Paris,FR -> ping.online.net (51.158.1.21) | min 0.651 avg 0.667 max 0.682 loss 0 | id 2VCd8geo8csS7XsUu00021UEx
XB IONOS Karlsruhe->OVH SBG | src IONOS AS8560 Karlsruhe,DE -> sbg.proof.ovh.net (51.91.75.40) | min 12.198 avg 12.293 max 12.442 loss 0 | id 2okgw6kQssL1ZSJYR00021UF4
XB IONOS Karlsruhe->OVH SBG | src IONOS AS8560 Karlsruhe,DE -> sbg.proof.ovh.net (51.91.75.40) | min 34.33 avg 34.4 max 34.571 loss 0 | id 2okgw6kQssL1ZSJYR00021UF4
XB Contabo Lauterbourg->OVH SBG | src Contabo AS51167 Lauterbourg,FR -> sbg.proof.ovh.net (51.91.75.40) | min 5.721 avg 5.854 max 6.493 loss 0 | id 2ZlHSXe0Z38d4Sqec00021UF4
XB velia Strasbourg->OVH SBG | src velia.net Internetdienste AS29066 Strasbourg,FR -> sbg.proof.ovh.net (51.91.75.40) | min 9.433 avg 10.012 max 13.647 loss 0 | id 2BfigbdbLvHPZTlBJ00021UF4
XB Offenburg->OVH SBG | src LEITWERK AS15894 Offenburg,DE -> sbg.proof.ovh.net (51.91.75.40) | min 7.113 avg 7.197 max 7.274 loss 0 | id 2mebMbXHmOzWCXG8w00021UF4
XB M247 Brussels->OVH RBX | src M247 AS9009 Brussels,BE -> rbx.proof.ovh.net (141.95.207.211) | min 11.798 avg 11.921 max 12.356 loss 0 | id 2Oxn9E2tIuXJi06UW00021UF4
XB Datacamp Brussels->OVH RBX | src Datacamp AS60068 Brussels,BE -> rbx.proof.ovh.net (141.95.207.211) | min 10.214 avg 10.291 max 10.454 loss 0 | id 2GiS9TRCOjnEnmZDq00021UF4
XB EDIS Brussels->OVH RBX | src EDIS AS57169 Brussels,BE -> rbx.proof.ovh.net (141.95.207.211) | min 11.499 avg 11.542 max 11.755 loss 0 | id 2JmTs4l0ep0vs6UAO00021UF4
XB OVH RBX->Datapacket BRU | src OVH AS16276 Roubaix,FR -> bru.download.datapacket.com (207.211.214.80) | min 10.005 avg 10.093 max 10.172 loss 0 | id 2UP1cyp454Z2ODrip00021UF4
XB Kortrijk->OVH RBX | src TeleNet AS6848 Kortrijk,BE -> rbx.proof.ovh.net (141.95.207.211) | min 18.899 avg 21.603 max 27.027 loss 0 | id 2abdF4gntn2SoZQq300021UF4
XB VNET Bratislava->Datapacket VIE | src VNET AS29405 Bratislava,SK -> vie.download.datapacket.com (156.146.61.131) | min 5.353 avg 5.414 max 5.489 loss 0 | id 2zrRan8CDlY0DLsgu00021UF4
XB eServer Bratislava->Datapacket VIE | src eServer AS61424 Bratislava,SK -> vie.download.datapacket.com (156.146.61.131) | min 5.254 avg 5.325 max 5.38 loss 0 | id 2hpWOXvTaplAJeojK00021UF4
XB Castlegem Bratislava->Datapacket VIE | src Castlegem AS34689 Bratislava,SK -> vie.download.datapacket.com (156.146.61.131) | min 5.482 avg 5.639 max 5.816 loss 0 | id 2llOoZXbsRA6J8TRq00021UF4
VIE netcup->Datapacket VIE | src netcup AS197540 Vienna,AT -> vie.download.datapacket.com (156.146.61.131) | min 1.012 avg 1.175 max 1.469 loss 0 | id 23V2YfMzzIWbH501c00021UF4
VIE HostHatch->Datapacket VIE | src HostHatch AS63473 Vienna,AT -> vie.download.datapacket.com (156.146.61.131) | min 25.734 avg 25.843 max 26.152 loss 0 | id 2gJCnwUwiugZ8hrbc00021UF4
VIE Exoscale->Datapacket VIE | src Akenes AS61098 Vienna,AT -> vie.download.datapacket.com (156.146.61.131) | min 0.749 avg 0.789 max 0.86 loss 0 | id 2CiYy5HEZ2v4xkTYj00021UF4
XB xTom Tallinn->Hetzner HEL | src xTom AS3214 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 56.89 avg 58.634 max 60.549 loss 0 | id 2HeUutDY5WpeUB5aa00021UF4
XB xTom Tallinn->Hetzner HEL | src xTom AS3214 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 54.6 avg 56.795 max 58.119 loss 0 | id 2HeUutDY5WpeUB5aa00021UF4
XB WaveCom Tallinn->Hetzner HEL | src WaveCom AS34702 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 2.038 avg 2.173 max 2.248 loss 0 | id 25RkHXTERz3hGETjS00021UF4
XB Telia Tallinn->Hetzner HEL | src Telia AS3249 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 7.435 avg 8.384 max 8.821 loss 0 | id 2ZgjqbcTaawXq77Q700021UF4
HEL UpCloud->Hetzner HEL | src UpCloud AS202053 Helsinki,FI -> hel1-speed.hetzner.com (95.217.255.81) | min 1.049 avg 1.125 max 1.209 loss 0 | id 2KWvGJuUhS6NX94yH00021UF4
HEL FlokiNET->Hetzner HEL | src FlokiNET AS200651 Helsinki,FI -> hel1-speed.hetzner.com (95.217.255.81) | min 0.968 avg 1.192 max 1.577 loss 0 | id 2BFmDS0RkDTZHZbOC00021UF4
XB Obehosting Malmo->Datapacket CPH | src Obehosting AS42675 Malmo,SE -> cph.download.datapacket.com (121.127.45.82) | min 21.207 avg 21.727 max 23.736 loss 0 | id 2SZWHrm3non3cv3X800021UF4
XB Obehosting Malmo->Datapacket CPH | src Obehosting AS42675 Malmo,SE -> cph.download.datapacket.com (121.127.45.82) | min 20.836 avg 21.02 max 21.123 loss 0 | id 2SZWHrm3non3cv3X800021UF4
CPH UpCloud->Datapacket CPH | src UpCloud AS202053 Copenhagen,DK -> cph.download.datapacket.com (121.127.45.82) | min 9.787 avg 9.808 max 9.858 loss 0 | id 2APmM2C8bbpGN1dyM00021UF4
XJ Infomaniak Geneva->Leaseweb FRA | src Infomaniak AS29222 Geneva,CH -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 15.666 avg 15.705 max 15.816 loss 0 | id 2mPjVCP7n9DChLYqm00021UF4
XJ Exoscale Zurich->Leaseweb FRA | src Akenes AS61098 Zurich,CH -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 5.847 avg 5.903 max 6.021 loss 0 | id 2YlqZl72HzxfAeFl600021UF4
XJ Init7 Zurich->Leaseweb FRA | src Init7 (Switzerland) AS13030 Zurich,CH -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 5.767 avg 5.827 max 5.876 loss 0 | id 2wADvWIoT9e6Q5JKh00021UF4
XJ Init7 Zurich->Clouvider FRA | src Init7 (Switzerland) AS13030 Zurich,CH -> fra.speedtest.clouvider.net (91.199.118.184) | min 16.705 avg 16.742 max 16.806 loss 0 | id 2y6v0N28fNXI4CRie00021UF4
XJ Leaseweb AMS->Leaseweb FRA | src LeaseWeb AS60781 Amsterdam,NL -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 6.625 avg 6.694 max 6.904 loss 0 | id 2doLjDsa6PtPei5Se00021UF5
XJ Scaleway AMS->Clouvider FRA | src SCALEWAY AS12876 Amsterdam,NL -> fra.speedtest.clouvider.net (91.199.118.184) | min 8.154 avg 8.859 max 11.418 loss 0 | id 2PYDRIxNErHNzAuMZ00021UF5
XJ FlokiNET Reykjavik->Vultr LON | src FlokiNET AS200651 Reykjavik,IS -> lon-gb-ping.vultr.com (108.61.196.101) | min 35.52 avg 35.688 max 36.007 loss 0 | id 2wUHirr4KNPx7exSX00021UF5
XJ FlokiNET Reykjavik->Leaseweb AMS | src FlokiNET AS200651 Reykjavik,IS -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 39.467 avg 39.537 max 39.677 loss 0 | id 2ecS83jSU3M5PFkf900021UF5
XJ FranTech Lux->Leaseweb FRA | src FranTech Solutions AS53667 Luxembourg,LU -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 13.308 avg 13.391 max 13.557 loss 0 | id 21bZYfGeHDwrplALy00021UF5
XJ FranTech Lux->OVH SBG | src FranTech Solutions AS53667 Luxembourg,LU -> sbg.proof.ovh.net (51.91.75.40) | min 7.865 avg 7.899 max 7.961 loss 0 | id 2T1VqpBCBMSPf0aj500021UF5
XJ Gcore Lux->Leaseweb FRA | src G-Core Labs AS202422 Luxembourg,LU -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 4.25 avg 4.275 max 4.332 loss 0 | id 2LkCsVtUpDFv5jBEL00021UF5
XB Hetzner FSN->Datapacket PRG | src Hetzner Online AS24940 Falkenstein,DE -> prg.download.datapacket.com (79.127.204.225) | min 11.926 avg 12.038 max 12.286 loss 0 | id 2EhaTG2twFKGjJwA800021UF5
XB Hetzner NBG->Datapacket PRG | src Hetzner Online AS24940 Nuremberg,DE -> prg.download.datapacket.com (152.233.26.50) | min 10.458 avg 10.597 max 10.997 loss 0 | id 2wD0s0DqKXaSBn1Fb00021UF5
XB Karlovy Vary->Hetzner FSN | src CC INTERNET AS202921 Karlovy Vary,CZ -> fsn1-speed.hetzner.com (78.46.170.2) | min 15.65 avg 18.418 max 22.326 loss 0 | id 2neiDfaq4ZUKTiHRS00021UF5
XB Init7 Basel->OVH SBG | src Init7 (Switzerland) AS13030 Basel,CH -> sbg.proof.ovh.net (51.91.75.40) | min 10.256 avg 10.408 max 10.694 loss 0 | id 2STzqKtCNNlVZDEdR00021UF5
XB Terabix Johor->Vultr SGP | src Terabix AS137552 Johor Bahru,MY -> sgp-ping.vultr.com (45.32.100.168) | min 1.895 avg 14.425 max 37.177 loss 0 | id 2bKwOBLkhbIiGNChh00021UF5
XB Advin Johor->Vultr SGP | src Advin Services AS206216 Johor Bahru,MY -> sgp-ping.vultr.com (45.32.100.168) | min 2.514 avg 17.39 max 38.383 loss 0 | id 2ov3UqLPsN4bK1Mi300021UF5
XJ OVH SBG probe->Leaseweb FRA | src OVH AS16276 Strasbourg,FR -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 4.47 avg 4.507 max 4.557 loss 0 | id 2z87jWOkmoApkx5DS00021UF5
XJ OVH RBX->Leaseweb AMS | src OVH AS16276 Roubaix,FR -> speedtest.ams1.nl.leaseweb.net (95.211.20.80) | min 6.349 avg 6.466 max 6.537 loss 0 | id 2jblD85W6bs6x7MQq00021UF5
XJ OVH GRA->Vultr LON | src OVH AS16276 Gravelines,FR -> lon-gb-ping.vultr.com (108.61.196.101) | min 4.042 avg 4.071 max 4.117 loss 0 | id 2SqpYojbFvMpOshB700021UF5
LON OVH->Vultr | src OVH AS16276 London,GB -> lon-gb-ping.vultr.com (108.61.196.101) | min 4.604 avg 4.716 max 4.827 loss 0 | id 23C8wwCCrZr00PtxV00021UF5
LON OVH->Vultr | src OVH AS16276 London,GB -> lon-gb-ping.vultr.com (108.61.196.101) | min 2.315 avg 2.482 max 3.353 loss 0 | id 23C8wwCCrZr00PtxV00021UF5
LON OVH->Clouvider | src OVH AS16276 London,GB -> lon.speedtest.clouvider.net (5.180.211.133) | min 1.301 avg 1.387 max 1.47 loss 0 | id 2l732f3liwDGoeeKL00021UF5
LON OVH->Clouvider | src OVH AS16276 London,GB -> lon.speedtest.clouvider.net (5.180.211.133) | min 4.055 avg 4.191 max 4.324 loss 0 | id 2l732f3liwDGoeeKL00021UF5
LON OVH->Datapacket | src OVH AS16276 London,GB -> lon.download.datapacket.com (84.17.50.24) | min 9.185 avg 9.217 max 9.232 loss 0 | id 29WXS0OpokuKoicUD00021UF5
LON Leaseweb->Vultr | src LeaseWeb AS205544 London,GB -> lon-gb-ping.vultr.com (108.61.196.101) | min 1.683 avg 1.729 max 1.777 loss 0 | id 2YvIYazq0xhSoZGZb00021UF5
LON Leaseweb->Clouvider | src LeaseWeb AS205544 London,GB -> lon.speedtest.clouvider.net (5.180.211.133) | min 1.826 avg 1.952 max 2.257 loss 0 | id 2Go3AlL0vOuwjASrM00021UF5
LON Clouvider->Vultr | src Clouvider AS62240 London,GB -> lon-gb-ping.vultr.com (108.61.196.101) | min 2.199 avg 2.666 max 5.136 loss 0 | id 2MJrZBiOAIw1BLOdC00021UF5
LON Vultr->Clouvider | src The Constant Company AS20473 London,GB -> lon.speedtest.clouvider.net (5.180.211.133) | min 2.642 avg 2.732 max 2.88 loss 0 | id 2XGpXkI8TGreu5C7e00021UF5
ASH OVH->Leaseweb | src OVH AS16276 Reston,US -> mirror.wdc1.us.leaseweb.net (207.244.94.80) | min 2.154 avg 2.288 max 2.553 loss 0 | id 2aKHW2ZIxN40siYwJ00021UF5
ASH OVH->Leaseweb | src OVH AS16276 Reston,US -> mirror.wdc1.us.leaseweb.net (207.244.94.80) | min 2.171 avg 2.183 max 2.2 loss 0 | id 2aKHW2ZIxN40siYwJ00021UF5
ASH OVH->Hetzner | src OVH AS16276 Reston,US -> ash-speed.hetzner.com (5.161.7.195) | min 1.711 avg 1.764 max 1.863 loss 0 | id 2tpHaVZ8qwoPkX3Ph00021UF5
ASH OVH->Hetzner | src OVH AS16276 Reston,US -> ash-speed.hetzner.com (5.161.7.195) | min 2.044 avg 2.085 max 2.131 loss 0 | id 2tpHaVZ8qwoPkX3Ph00021UF5
ASH OVH->Clouvider | src OVH AS16276 Reston,US -> ash.speedtest.clouvider.net (45.250.25.133) | min 1.527 avg 1.604 max 1.664 loss 0 | id 2QVUOUGAsyOUoeRnu00021UF5
ASH OVH->Datapacket | src OVH AS16276 Reston,US -> ash.download.datapacket.com (109.61.91.194) | min 2.332 avg 2.36 max 2.405 loss 0 | id 2VgVLZIOpY9M5VkWf00021UF5
ASH Leaseweb->Hetzner | src LeaseWeb AS30633 Manassas,US -> ash-speed.hetzner.com (5.161.7.195) | min 1.182 avg 1.246 max 1.386 loss 0 | id 2PH4WFrStZrB4yR8L00021UF5
ASH Leaseweb->Hetzner | src LeaseWeb AS30633 Manassas,US -> ash-speed.hetzner.com (5.161.7.195) | min 1.337 avg 1.449 max 1.91 loss 0 | id 2PH4WFrStZrB4yR8L00021UF5
ASH Leaseweb->OVH | src LeaseWeb AS30633 Manassas,US -> vin.proof.ovh.us (135.148.100.133) | min 2.625 avg 2.734 max 2.843 loss 0 | id 2lHTRgKXRYdRdwgYu00021UF5
ASH Leaseweb->OVH | src LeaseWeb AS30633 Manassas,US -> vin.proof.ovh.us (135.148.100.133) | min 2.28 avg 2.402 max 2.543 loss 0 | id 2lHTRgKXRYdRdwgYu00021UF5
ASH Leaseweb->Clouvider | src LeaseWeb AS30633 Manassas,US -> ash.speedtest.clouvider.net (45.250.25.133) | min 1.179 avg 1.434 max 2.302 loss 0 | id 2wqFuoRymHSRLeej000021UF5
ASH Clouvider->Hetzner | src Clouvider AS62240 Ashburn,US -> ash-speed.hetzner.com (5.161.7.195) | min 0.429 avg 0.509 max 0.592 loss 0 | id 2jhkwAJoAEAqmY7bF00021UF5
ASH Clouvider->Leaseweb | src Clouvider AS62240 Ashburn,US -> mirror.wdc1.us.leaseweb.net (207.244.94.80) | min 1.18 avg 1.257 max 1.374 loss 0 | id 2a1T1GmxVPjfYuuz300021UF5
ASH Clouvider->OVH | src Clouvider AS62240 Ashburn,US -> vin.proof.ovh.us (135.148.100.133) | min 1.992 avg 2.046 max 2.08 loss 0 | id 2EuWxyydcYJiQZK1y00021UF5
NYC Vultr NJ->Clouvider NYC | src The Constant Company AS20473 Piscataway,US -> nyc.speedtest.clouvider.net (194.33.45.192) | min 2.124 avg 2.418 max 2.836 loss 0 | id 2BIpXkg3OhnbpA8se00021UF5
NYC ReliableSite->Vultr NJ | src ReliableSite.Net AS23470 Piscataway,US -> nj-us-ping.vultr.com (108.61.149.182) | min 0.876 avg 0.985 max 1.134 loss 0 | id 2Qs9EYjDeqSzYPZSc00021UF5
NYC ReliableSite NY->Clouvider NYC | src ReliableSite.Net AS23470 New York,US -> nyc.speedtest.clouvider.net (194.33.45.192) | min 2.193 avg 2.223 max 2.36 loss 0 | id 2A8MaDywRIQF9NZDu00021UF5
NYC Hivelocity NY->Vultr NJ | src Hivelocity AS29802 New York,US -> nj-us-ping.vultr.com (108.61.149.182) | min 1.694 avg 1.756 max 1.833 loss 0 | id 2ITEc01KU4Xe0uqPj00021UF5
NYC Hivelocity NY->Clouvider NYC | src Hivelocity AS29802 New York,US -> nyc.speedtest.clouvider.net (194.33.45.192) | min 2.134 avg 2.164 max 2.21 loss 0 | id 2grqSEzNXCzXmd6gg00021UF5
NYC HostHatch NY->Clouvider NYC | src HostHatch AS63473 New York,US -> nyc.speedtest.clouvider.net (194.33.45.192) | min 0.9 avg 0.982 max 1.095 loss 0 | id 2wN83O8qi7QrBKh9b00021UF5
NBG netcup->Leaseweb FRA | src netcup AS197540 Nuremberg,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 3.637 avg 3.764 max 3.9 loss 0 | id 20e5v1dubi7RlkxjA00021UF5
FRA xTom->Leaseweb | src xTom AS3214 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.253 avg 1.437 max 1.574 loss 0 | id 2VzG2to0GD3uB3xlp00021UF5
FRA dataforest->Leaseweb | src dataforest AS58212 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 0.764 avg 0.99 max 1.241 loss 0 | id 2J5jx5H1wDnR1pq3a00021UF5
XB InfoNet Tallinn->Hetzner HEL | src InfoNet AS8728 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 12.467 avg 12.985 max 14.843 loss 0 | id 2ogWyYwHctq3ecaie00021UF6
XB HostSlim Tallinn->Hetzner HEL | src HostSlim AS207083 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 1.992 avg 2.033 max 2.064 loss 0 | id 23pSJCPjtHlCotZNi00021UF6
XB Tele2 Tallinn->Hetzner HEL | src Tele2 AS1257 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 35.394 avg 35.811 max 37.901 loss 0 | id 22iwNlVRO4Qu3cWoU00021UF6
XB WaveCom Tallinn->Hetzner HEL (repeat) | src WaveCom AS34702 Tallinn,EE -> hel1-speed.hetzner.com (95.217.255.81) | min 2.123 avg 2.194 max 2.238 loss 0 | id 2xrFRTFzLNJURoG4l00021UF6
NBG netcup->Hetzner (repeat) | src netcup AS197540 Nuremberg,DE -> nbg1-speed.hetzner.com (78.47.119.196) | min 0.398 avg 0.459 max 0.555 loss 0 | id 2fqOzy1eq71rPIkdZ00021UF6
NBG netcup->Hetzner (repeat) | src netcup AS197540 Nuremberg,DE -> nbg1-speed.hetzner.com (78.47.119.196) | min 0.397 avg 1.239 max 6.656 loss 0 | id 2fqOzy1eq71rPIkdZ00021UF6
NBG netcup->Hetzner (repeat) | src netcup AS197540 Nuremberg,DE -> nbg1-speed.hetzner.com (78.47.119.196) | min 0.421 avg 0.477 max 0.546 loss 0 | id 2fqOzy1eq71rPIkdZ00021UF6
CHI Hivelocity->Vultr | src Hivelocity AS29802 Chicago,US -> il-us-ping.vultr.com (107.191.51.12) | min 1.758 avg 2.61 max 7.638 loss 0 | id 2Gxj0inXVaKmErW5300021UF6
CHI FDC->Vultr | src FDCservers.net AS30058 Chicago,US -> il-us-ping.vultr.com (107.191.51.12) | min 0.938 avg 0.965 max 1.035 loss 0 | id 2faFH8MaGk2gXVFOh00021UF6
CHI HostHatch->Vultr | src HostHatch AS63473 Chicago,US -> il-us-ping.vultr.com (107.191.51.12) | min 1.575 avg 1.673 max 1.916 loss 0 | id 2XJ2PPi3sFpwZAXeK00021UF6
DAL Datacamp->Vultr | src Datacamp AS60068 Dallas,US -> tx-us-ping.vultr.com (108.61.224.175) | min 0.366 avg 0.514 max 1.006 loss 0 | id 2vX4lnIvXYUGHb0pN00021UF7
DAL Linode->Vultr | src Akamai Connected Cloud AS63949 Dallas,US -> tx-us-ping.vultr.com (108.61.224.175) | min 0.968 avg 1.064 max 1.141 loss 0 | id 2WTezNCR60ADyuQar00021UF7
LAX ReliableSite->Vultr | src ReliableSite.Net AS23470 Los Angeles,US -> lax-ca-us-ping.vultr.com (108.61.219.200) | min 0.284 avg 0.342 max 0.413 loss 0 | id 28dJYTJGtDm112fVQ00021UF7
LAX HostHatch->Vultr | src HostHatch AS63473 Los Angeles,US -> lax-ca-us-ping.vultr.com (108.61.219.200) | min 0.522 avg 0.639 max 0.838 loss 0 | id 27vv0txRj6qY8s32000021UF7
LAX OVH->Vultr | src OVH AS16276 Los Angeles,US -> lax-ca-us-ping.vultr.com (108.61.219.200) | min 0.416 avg 0.481 max 0.701 loss 0 | id 2O9rx3lMOg1Hpois200021UF7
SJC xTom->Vultr | src xTom AS6233 San Jose,US -> sjo-ca-us-ping.vultr.com (104.156.230.107) | min 1.095 avg 1.372 max 2.892 loss 0 | id 2fdXMZ2WJnnTlc2Ku00021UF7
SJC DO->Vultr | src DigitalOcean AS14061 Santa Clara,US -> sjo-ca-us-ping.vultr.com (104.156.230.107) | min 0.999 avg 1.57 max 2.993 loss 0 | id 2WQ9iymYwy066IdcA00021UF7
SGP OVH->Vultr | src OVH AS16276 Singapore,SG -> sgp-ping.vultr.com (45.32.100.168) | min 1.347 avg 14.041 max 64.213 loss 0 | id 2ALG2nploku61uD0v00021UF7
SGP OVH->Vultr | src OVH AS16276 Singapore,SG -> sgp-ping.vultr.com (45.32.100.168) | min 1.542 avg 5.402 max 11.623 loss 0 | id 2ALG2nploku61uD0v00021UF7
SGP DO->Vultr | src DigitalOcean AS14061 Singapore,SG -> sgp-ping.vultr.com (45.32.100.168) | min 1.355 avg 18.443 max 87.266 loss 12.5 | id 2LyCdnVEROZ8ihKB600021UF7
SGP Linode->Vultr | src Akamai Connected Cloud AS63949 Singapore,SG -> sgp-ping.vultr.com (45.32.100.168) | min 1.062 avg 4.845 max 18.803 loss 0 | id 2ICMNe0Ckpasmn7Os00021UF7
FRA OVH->Leaseweb (repeat) | src OVH AS16276 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.554 avg 1.562 max 1.576 loss 0 | id 2gKwSpr2KPfIzSBL300021UF7
FRA OVH->Leaseweb (repeat) | src OVH AS16276 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.49 avg 1.539 max 1.655 loss 0 | id 2gKwSpr2KPfIzSBL300021UF7
FRA OVH->Leaseweb (repeat) | src OVH AS16276 Frankfurt,DE -> speedtest.fra1.de.leaseweb.net (178.162.226.176) | min 1.606 avg 1.656 max 1.719 loss 0 | id 2gKwSpr2KPfIzSBL300021UF7
AMS Leaseweb->Scaleway (repeat) | src LeaseWeb AS60781 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 0.306 avg 0.353 max 0.405 loss 0 | id 2LsDzBGO7QJGndLmv00021UF7
AMS Leaseweb->Scaleway (repeat) | src LeaseWeb AS60781 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 0.4 avg 0.437 max 0.466 loss 0 | id 2LsDzBGO7QJGndLmv00021UF7
AMS Leaseweb->Scaleway (repeat) | src LeaseWeb AS60781 Amsterdam,NL -> ping-ams1.online.net (163.172.208.7) | min 0.795 avg 0.881 max 0.961 loss 0 | id 2LsDzBGO7QJGndLmv00021UF7
PAR Vultr->Scaleway (repeat) | src The Constant Company AS20473 Paris,FR -> ping.online.net (51.158.1.21) | min 0.715 avg 0.786 max 0.888 loss 0 | id 2X9ulOohEIV5VAHca00021UF7
PAR Vultr->Scaleway (repeat) | src The Constant Company AS20473 Paris,FR -> ping.online.net (51.158.1.21) | min 0.641 avg 0.727 max 0.786 loss 0 | id 2X9ulOohEIV5VAHca00021UF7
ASH Clouvider->Hetzner (repeat) | src Clouvider AS62240 Ashburn,US -> ash-speed.hetzner.com (5.161.7.195) | min 0.408 avg 0.463 max 0.503 loss 0 | id 2ZTYztenckAFKOtBY00021UF7
ASH Clouvider->Hetzner (repeat) | src Clouvider AS62240 Ashburn,US -> ash-speed.hetzner.com (5.161.7.195) | min 0.49 avg 0.557 max 0.673 loss 0 | id 2ZTYztenckAFKOtBY00021UF7
HEL UpCloud->Hetzner HEL (repeat) | src UpCloud AS202053 Helsinki,FI -> hel1-speed.hetzner.com (95.217.255.81) | min 0.962 avg 1.066 max 1.213 loss 0 | id 2hq0IfJQQ0VMbZKlC00021UF7
FRA Leaseweb->Clouvider (repeat) | src LeaseWeb AS28753 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.726 avg 0.78 max 0.837 loss 0 | id 2zWHjHJtq2iLowNOZ00021UF7
FRA Leaseweb->Clouvider (repeat) | src LeaseWeb AS28753 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.639 avg 0.694 max 0.749 loss 0 | id 2zWHjHJtq2iLowNOZ00021UF7
FRA Leaseweb->Clouvider (repeat) | src LeaseWeb AS28753 Frankfurt,DE -> fra.speedtest.clouvider.net (91.199.118.184) | min 0.65 avg 0.696 max 0.787 loss 0 | id 2zWHjHJtq2iLowNOZ00021UF7
XB Hetzner HEL->wavecom.ee (Tallinn) | src Hetzner Online AS24940 Helsinki,FI -> wavecom.ee (80.79.112.30) | min None avg None max None loss 100 | id 27xiiaArnkWXTZDRZ00021UFC
XB Hetzner HEL->wavecom.ee (Tallinn) | src Hetzner Online AS24940 Helsinki,FI -> wavecom.ee (80.79.112.30) | min None avg None max None loss 100 | id 27xiiaArnkWXTZDRZ00021UFC
XB UpCloud HEL->wavecom.ee (Tallinn) | src UpCloud AS202053 Helsinki,FI -> wavecom.ee (80.79.112.30) | min None avg None max None loss 100 | id 2naoYdK616oXF19Il00021UFC
XB FlokiNET HEL->wavecom.ee (Tallinn) | src FlokiNET AS200651 Helsinki,FI -> wavecom.ee (80.79.112.30) | min None avg None max None loss 100 | id 2kPnp9mUVdoQSRV1H00021UFC
XB netcup Vienna->vnet.sk (Bratislava) | src netcup AS197540 Vienna,AT -> www.vnet.sk (217.73.28.12) | min 12.795 avg 12.857 max 12.93 loss 0 | id 2sP36VbneV5UCX6Fm00021UFC
XB netcup Vienna->vnet.sk (Bratislava) | src netcup AS197540 Vienna,AT -> www.vnet.sk (217.73.28.12) | min 12.872 avg 12.962 max 13.013 loss 0 | id 2sP36VbneV5UCX6Fm00021UFC
XB Exoscale Vienna->vnet.sk (Bratislava) | src Akenes AS61098 Vienna,AT -> www.vnet.sk (217.73.28.12) | min 23.116 avg 23.202 max 23.267 loss 0 | id 278onOyYbGhAjNlBA00021UFC
XB Anexia Vienna->vnet.sk (Bratislava) | src Anexia Cloud Solutions AS40980 Vienna,AT -> www.vnet.sk (217.73.28.12) | min 19.646 avg 20.102 max 20.729 loss 0 | id 2yLlGWgu6jmVu9L0S00021UFC
```
