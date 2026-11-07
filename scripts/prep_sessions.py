"""Convert data/sessions_utrecht_raw.csv to data/sessions_utrecht_filtered.csv.
Local times are converted to UTC; timestamps in the DST change hour are
dropped. The requested energy is the delivered energy."""
import pandas as pd

RAW_PATH = 'data/sessions_utrecht_raw.csv'
OUT_PATH = 'data/sessions_utrecht_filtered.csv'
TZ = 'Europe/Amsterdam'
GMT_FMT = '%a, %d %b %Y %H:%M:%S GMT'


def to_utc(naive):
    return naive.dt.tz_localize(TZ, ambiguous='NaT', nonexistent='NaT').dt.tz_convert('UTC')


df = pd.read_csv(RAW_PATH, sep=';', parse_dates=['start_datetime', 'end_datetime'])
df['start_utc'] = to_utc(df['start_datetime'])
df['end_utc'] = to_utc(df['end_datetime'])
df = df.dropna(subset=['start_utc', 'end_utc']).copy()
df = df[df['total_energy'] > 0].copy()
df = df[df['end_utc'] > df['start_utc']].copy()

out = pd.DataFrame({
    'userID': df['EV_id_x'],
    'sessionID': df['EV_id_x'] + '_' + df.groupby('EV_id_x').cumcount().astype(str),
    'stationID': df['evse_uid'],
    'connectionTime': df['start_utc'].dt.strftime(GMT_FMT),
    'disconnectTime': df['end_utc'].dt.strftime(GMT_FMT),
    'kWhDelivered': df['total_energy'],
    'kWhRequested': df['total_energy'],
    'minutesAvailable': (df['end_utc'] - df['start_utc']).dt.total_seconds() / 60.0,
    'timezone': TZ,
})
out.to_csv(OUT_PATH, index=False)
print(f'{len(out)} sessions -> {OUT_PATH}')
