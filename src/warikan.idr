module warikan

import Data.Vect

%access public export

飲み会名 : Type
飲み会名 = String

開催日時 : Type
開催日時 = String

参加者名 : Type
参加者名 = String

請求金額 : Type
請求金額 = Integer

支払金額 : Type
支払金額 = Integer

data 支払える具合 = ちょっと払える
                | 普通に払える
                | 結構払える
                | 幹事

record 参加者 where
  constructor 参加者になる
  name : 参加者名
  shiharai : 支払える具合

record 飲み会 where
  constructor 飲み会作る
  nomikaiName : 飲み会名
  nomikaiDate : 開催日時
  sankashas   : Vect n 参加者

参加者を足す : (name : 飲み会名) -> (shiharai : 支払える具合) -> (xs : Vect n 参加者) -> Vect (S n) 参加者
参加者を足す n s xs = (参加者になる n s) :: xs

企画する : (kName : 参加者名) -> (nName : 飲み会名) -> (date : 開催日時) -> 飲み会
企画する kName nName date = 飲み会作る nName date (参加者を足す kName 幹事 [])  

参加する : (sName : 参加者名) -> (shiharai : 支払える具合) -> (nomikai : 飲み会) -> 飲み会
参加する sName shiharai nomikai = record { sankashas $= ((参加者になる sName shiharai) ::) } nomikai

data 割り勘できる : (xs : Vect n a) -> Type where
  できるんだよ : 割り勘できる (x::xs)

-- empty なら矛盾にする
Uninhabited (割り勘できる []) where
  uninhabited できるんだよ impossible

割り勘できるんか : (xs : Vect n a) -> Dec (割り勘できる xs)
割り勘できるんか [] = No absurd -- Nil なら矛盾してる
割り勘できるんか (x::xs) = Yes できるんだよ -- Nil 以外は T

割り勘 : (okaikei : 請求金額) -> (xs : Vect n 参加者) -> {auto ok : 割り勘できる xs} -> 支払金額
割り勘 _ [] {ok=できるんだよ} impossible
割り勘 m (x::xs) {ok=p} = m

