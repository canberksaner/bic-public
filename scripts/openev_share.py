"""Share of current passenger cars and SUVs with a CCS2 inlet and a battery of
at least 30 kWh whose AC rating is 11 or 22 kW (OpenEV Data v1.24.0, Sec. II)."""
import json

with open('data/open-ev-data-v1.24.0.json', encoding='utf-8') as f:
    vehicles = json.load(f)['vehicles']


def battery_kwh(v):
    b = v['battery']
    net = b.get('pack_capacity_kwh_net')
    return net if net is not None else b.get('pack_capacity_kwh_gross')


def ac_kw(v):
    return (v['charging'].get('ac') or {}).get('max_power_kw')


sel = [v for v in vehicles
       if (v.get('availability') or {}).get('status') == 'production'
       and any(p['connector'] == 'ccs2' for p in v['charge_ports'])
       and v['vehicle_type'] in ('passenger_car', 'suv')
       and battery_kwh(v) is not None and battery_kwh(v) >= 30.0
       and ac_kw(v) is not None]
k = sum(ac_kw(v) in (11.0, 22.0) for v in sel)
print(f'{k} of {len(sel)} records ({100 * k / len(sel):.1f}%) have an AC rating of 11 or 22 kW')
