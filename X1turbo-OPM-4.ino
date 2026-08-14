// VGMファイルから曲データを読み込んで、YM2151から音を出す
// 再生するVGMファイルはSDカードに格納しておいてくださいな
// Copyright (c) 2026 Mugio (mugio_ch)
// This software is released under the MIT License, see LICENSE.

// +GPIOピン節約するためにボタンを分圧で接続
// +WiFi機能を無効に
//  release version 1.1 at 2026.07.26
#include <Arduino.h>
#include <FS.h>
#include <SD.h>
#include <Wire.h>
#include <Adafruit_SSD1306.h>
#include "hal/gpio_ll.h"
#include "driver/ledc.h"
#include <WiFi.h>

#define SCREEN_WIDTH 128 // OLED display width, in pixels
#define SCREEN_HEIGHT 32 // OLED display height, in pixels
#define OLED_RESET     -1 // Reset pin # (or -1 if sharing Arduino reset pin)
#define SCREEN_ADDRESS 0x3C ///< See datasheet for Address; 0x3D for 128x64, 0x3C for 128x32

// --- ピン定義 ---
//GPIO 10,11,12,13,14 SD Card
//GPIO  0, 3,45,46 Boot Strapping
//GPIO 19,20 USB
//GPIO 43,44 UART
//GPIO 35,36,37 PSRAM
//GPIO 48 LED

//YM2151 Control
const int PIN_D[8] =  {4, 5, 6, 7, 15, 16, 17, 18}; // D0～D7
const int OPM_CLK  =  1;  // 3.579545 MHz (または4MHz)
const int OPM_A0   =  2;  // アドレス / データ 選択 
const int OPM_WR   = 42;  // ライト信号
const int OPM_CS   = 41;  // チップセレクト
const int OPM_IC   = 40;  // イニシャルクリア (リセット)
// //YM2151 Control
const int PSG_CLK  = 39;  // 2MHz (または1.99872MHz)
const int PSG_BC1  = 20;  // Bus Control 1
const int PSG_BDIR = 21;  // Bus Direction
const int PSG_RESET= 47;  // リセット信号 (必要に応じて)
//etc.
const int SD_CS     = 10;
const int I2C_SDA   =  8;
const int I2C_SCL   =  9;
const int BTN_ADC_PIN = 14;

// --- ボタンIDの定義 ---
enum ButtonID {
  BTN_NONE = 0,
  BTN_1_ID,
  BTN_2_ID,
  BTN_3_ID,
  BTN_4_ID
};

// --- 抵抗分圧のADC閾値設定 (ESP32: 12bit / 0～4095) ---
const int BTN1_ADC_VAL =    0; // BTN1 押下時のADC値
const int BTN2_ADC_VAL =  830; // BTN2 押下時のADC値
const int BTN3_ADC_VAL = 1630; // BTN3 押下時のADC値
const int BTN4_ADC_VAL = 3040; // BTN4 押下時のADC値
const int ADC_MARGIN   =  200; // 許容誤差（±200）

// --- 高速レジスタ操作用の配線マスク定義 ---
// D0~D7が使用する全GPIOピンのビット論理和（マスク）をあらかじめ計算しておく
// GPIO 4, 5, 6, 7, 15, 16, 17, 18
const uint32_t BUS_PIN_MASK = (1ULL << 4)  | (1ULL << 5)  | (1ULL << 6)  | (1ULL << 7) |
                              (1ULL << 15) | (1ULL << 16) | (1ULL << 17) | (1ULL << 18);

// 8ビットのデータ（0〜255）を各GPIOのビット配置へ一瞬で変換するためのルックアップテーブル（LUT）
// 毎回ビットシフトのループを回すと遅いため、256バイトの配列としてPSRAMや内蔵RAMに展開します。
uint32_t data_to_gpio_lut[256];

// --- グローバル変数 ---
//File vgmFile;
bool isPlaying = false;
uint8_t* vgm_data_buffer = NULL; // PSRAM上のVGM全データバッファ
size_t vgm_file_size = 0;        // ファイルの総サイズ
size_t vgm_ptr = 0;              // 現在の読み込みファイルポインタ（インデックス）
uint8_t current_block_id;
uint32_t vgm_loop_offset = 0; 
uint8_t vgm_loop_count = 0;
uint8_t vgm_loops = 2;
uint64_t next_vgm_execute_us = 0;

Adafruit_SSD1306 display(SCREEN_WIDTH, SCREEN_HEIGHT, &Wire, OLED_RESET);

// --- 状態管理用 ---
enum Mode { MODE_SELECT_DIR, MODE_SELECT_FILE };
Mode currentMode = MODE_SELECT_DIR;
String currentDir = "/"; // 現在表示中のフォルダパス
std::vector<String> dirList;  // フォルダ一覧
std::vector<String> fileList; // ファイル一覧
int dirIndex = 0;
int fileIndex = 0;

// ADPCMデータの一時格納バッファ (0x67コマンド用)
#define MAX_ADPCM_Block 16
struct AdpcmBlock {
  uint8_t* buffer = NULL;
  size_t length = 0;
};
AdpcmBlock ADPCM_Blocks[MAX_ADPCM_Block];
// --- 割り込み同期用の変数（volatile指定が必須） ---
volatile uint8_t* adpcm_play_ptr = NULL;
volatile size_t adpcm_remaining_bytes = 0;

// --- ハードウェア制御関数群 ---
// --- 高速化されたデータバス書き込み関数 ---
void IRAM_ATTR writeDataBus(uint8_t value) {
  // 1. ルックアップテーブルから、この値に対応するGPIOのビットパターン（Hにすべきピン）を一瞬で取得
  uint32_t set_mask = data_to_gpio_lut[value];
  
  // 2. 逆に、Lにすべきピンのマスクを計算（全バスピンのうち、Hにならないピン）
  uint32_t clear_mask = BUS_PIN_MASK & (~set_mask);

  // 3. レジスタへ直接書き込み（1〜2クロックで全ピンが同時に確定する）
  // ※ESP32-S3のGPIO 0〜31は GPIO.out_w1ts / w1tc で制御します
  GPIO.out_w1tc = clear_mask; // Lにしたいピンを同時に引き下げる
  GPIO.out_w1ts = set_mask;   // Hにしたいピンを同時に引き上げる
}

// 配列から1バイト読み込む代替関数
uint8_t readVgmByte() {
  if (vgm_ptr < vgm_file_size) {
    return vgm_data_buffer[vgm_ptr++];
  }
  return 0x66; // 万が一範囲を超えたらEndコマンドを返す
}

// 配列から複数バイト読み込む代替関数
void readVgmBytes(uint8_t* dest, size_t len) {
  if (vgm_ptr + len <= vgm_file_size) {
    memcpy(dest, &vgm_data_buffer[vgm_ptr], len);
    vgm_ptr += len;
  }
}

// YM2151にデータを書き込む
void writeOPM(uint8_t reg, uint8_t data) {
  portDISABLE_INTERRUPTS(); // OPM書き込み中、データバスを独占する
  digitalWrite(OPM_A0, LOW);
  writeDataBus(reg);// write
  digitalWrite(OPM_CS, LOW); 
  digitalWrite(OPM_WR, LOW);
  delayMicroseconds(1);
  digitalWrite(OPM_WR, HIGH); 
  digitalWrite(OPM_CS, HIGH);
  delayMicroseconds(2); 
  digitalWrite(OPM_A0, HIGH);
  writeDataBus(data);// write
  digitalWrite(OPM_CS, LOW); 
  digitalWrite(OPM_WR, LOW);
  delayMicroseconds(1);
  digitalWrite(OPM_WR, HIGH); 
  digitalWrite(OPM_CS, HIGH);
  portENABLE_INTERRUPTS(); // 解放
  delayMicroseconds(10); 
}

// YM2149にデータを書き込む
void writePSG(uint8_t reg, uint8_t data) {
  portDISABLE_INTERRUPTS();
  // Step 1: アドレスラッチ (BDIR=1, BC1=1)
  digitalWrite(PSG_BC1, LOW);//inactive
  digitalWrite(PSG_BDIR, LOW);
  writeDataBus(reg & 0x0F);
  delayMicroseconds(2);
  digitalWrite(PSG_BC1, HIGH);//latch
  digitalWrite(PSG_BDIR, HIGH);
  delayMicroseconds(5);
  digitalWrite(PSG_BC1, LOW);//inactive
  digitalWrite(PSG_BDIR, LOW);
  delayMicroseconds(2);
  digitalWrite(PSG_BC1, LOW);//write
  digitalWrite(PSG_BDIR, HIGH);
  writeDataBus(data);
  delayMicroseconds(5);
  digitalWrite(PSG_BC1, LOW);//inactive
  digitalWrite(PSG_BDIR, LOW);
  delayMicroseconds(2);
  portENABLE_INTERRUPTS();
}

// VGMファイルのウェイト処理
void vgmWaitSamples(uint32_t samples) {
  if (samples == 0) return;

  // サンプル数から、待つべき正確なマイクロ秒（浮動小数点を用いて誤差を無くす）を計算し、目標時刻に加算
  next_vgm_execute_us += (uint64_t)((double)samples * 1000000.0 / 44100.0);

  // 目標時刻になるまでひたすら待つ（ビジーループ）
  while ((uint64_t)esp_timer_get_time() < next_vgm_execute_us) {
    // 1ミリ秒以上待つ必要がある場合は、他のタスク（WDTやシステム用）に一瞬だけ譲る
    if ((next_vgm_execute_us - esp_timer_get_time()) > 2000) {
      vTaskDelay(1); 
    } else {
      asm volatile("nop;"); // 短い時間はNOPで超精密に待つ
    }
  }
}

// GPIO書き込み処理
void initDataBusLUT() {
  for (int val = 0; val < 256; val++) {
    uint32_t gpio_bits = 0;
    if ((val >> 0) & 1) gpio_bits |= (1ULL << 4);  // D0 -> GPIO4
    if ((val >> 1) & 1) gpio_bits |= (1ULL << 5);  // D1 -> GPIO5
    if ((val >> 2) & 1) gpio_bits |= (1ULL << 6);  // D2 -> GPIO6
    if ((val >> 3) & 1) gpio_bits |= (1ULL << 7);  // D3 -> GPIO7
    if ((val >> 4) & 1) gpio_bits |= (1ULL << 15); // D4 -> GPIO15
    if ((val >> 5) & 1) gpio_bits |= (1ULL << 16); // D5 -> GPIO16
    if ((val >> 6) & 1) gpio_bits |= (1ULL << 17); // D6 -> GPIO17
    if ((val >> 7) & 1) gpio_bits |= (1ULL << 18); // D7 -> GPIO18
    
    data_to_gpio_lut[val] = gpio_bits;
  }
}

// リトルエンディアン処理
uint32_t readLE(uint8_t* buf, size_t size) {
  uint32_t val = 0;
  for (size_t i = 0; i < size; i++) {
    val |= (buf[i] << (8 * i));
  }
  return val;
}

// セットアップ
void setup() {
  WiFi.disconnect(true);
  Serial.begin(115200);
  Wire.begin(I2C_SDA, I2C_SCL);
  Serial.println("Wire_begin");
  display.begin(SSD1306_SWITCHCAPVCC, SCREEN_ADDRESS);
  Serial.println("SSD1306_begin");
  display.clearDisplay();
  display.setTextSize(1);
  display.setTextColor(SSD1306_WHITE);

  if (!SD.begin(SD_CS)) {
    Serial.println("Card Mount Failed");
    return;
  }

  pinMode(BTN_ADC_PIN, INPUT);
  analogReadResolution(12); // 12bit分解能 (0~4095)

  // YM2149 PSG 制御ピンの初期化
  pinMode(PSG_BDIR, OUTPUT); 
  pinMode(PSG_BC1, OUTPUT);
  digitalWrite(PSG_BDIR, LOW); 
  digitalWrite(PSG_BC1, LOW);
  // YM2151 OPM 制御ピンの初期化
  pinMode(OPM_A0, OUTPUT); 
  pinMode(OPM_WR, OUTPUT); 
  pinMode(OPM_CS, OUTPUT); 
  pinMode(OPM_IC, OUTPUT);
  digitalWrite(OPM_CS, HIGH); 
  digitalWrite(OPM_WR, HIGH); 
  digitalWrite(OPM_A0, HIGH);

  // GPIOからクロック出力
  pinMode(OPM_CLK, OUTPUT); 
  pinMode(PSG_CLK, OUTPUT); 
  initClocks();

  // D0-D7向けのピン初期化
  for (int i = 0; i < 8; i++) {
    pinMode(PIN_D[i], OUTPUT);
  }
  // YM2151を初期化
  Serial.println("Resetting YM2151..."); 
  digitalWrite(OPM_IC, LOW);
  delay(50);
  digitalWrite(OPM_IC, HIGH);
  // YM2149を初期化
  Serial.println("Resetting YM2149..."); 
  digitalWrite(PSG_RESET, LOW);
  delay(50);
  digitalWrite(PSG_RESET, HIGH);
  delay(50);
  // 初期の消音状態を設定
  muteAll();

  // 初回のファイルリスト取得と描画
  updateLists();
  drawDisplay();
  initDataBusLUT();//データバス用レジスタの初期化
}

// --- メインループ ---
void loop(){
  bool changed = false;

  if (!isPlaying) {
  // ボタン1: 次へ (旧: BTN2 -> BTN_2_ID)
  if (checkButton(BTN_2_ID)) {
    if (currentMode == MODE_SELECT_DIR && !dirList.empty()) {
      dirIndex = (dirIndex + 1) % dirList.size();
      if (dirList[dirIndex] == "System Volume Information") dirIndex = 0;
    } else if (currentMode == MODE_SELECT_FILE && !fileList.empty()) {
      fileIndex = (fileIndex + 1) % fileList.size();
    }
    changed = true;
  }

  // ボタン2: 前へ (旧: BTN1 -> BTN_1_ID)
  if (checkButton(BTN_1_ID)) {
    if (currentMode == MODE_SELECT_DIR && !dirList.empty()) {
      dirIndex = (dirIndex - 1 + dirList.size()) % dirList.size();
      if(dirIndex == 1) dirIndex = 0;
    } else if (currentMode == MODE_SELECT_FILE && !fileList.empty()) {
      fileIndex = (fileIndex - 1 + fileList.size()) % fileList.size();
    }
    changed = true;
  }

  // ボタン3: 決定 (旧: BTN3 -> BTN_3_ID)
  if (checkButton(BTN_3_ID)) {
    if (currentMode == MODE_SELECT_DIR) {
      if (!dirList.empty()) {
        if (dirList[dirIndex] == "[ root ]") {
          currentDir = "/";
        } else {
          currentDir = "/" + dirList[dirIndex] + "/";
        }
        currentMode = MODE_SELECT_FILE;
        fileIndex = 0;
        updateLists();
      }
    } else if (currentMode == MODE_SELECT_FILE) {
      if (!fileList.empty()) {
        String fullPath = currentDir + fileList[fileIndex];
        loadFileToPSRAM(fullPath);
      }
    }
    changed = true;
  }

  // ボタン4: 戻る (旧: BTN4 -> BTN_4_ID)
  if (checkButton(BTN_4_ID)) {
    if (currentMode == MODE_SELECT_FILE) {
      currentMode = MODE_SELECT_DIR;
      changed = true;
    }
  }

    if (!isPlaying && changed) {
      drawDisplay();
    }
    delay(10); // チャタリング防止用小休止
  } else {

    VGM_parser();
  }
}

//VGMファイルを読み込んで演奏開始
void PSRAM_use(){ 
  // VGMヘッダ解析 (メモリ上で行う)
  uint8_t offsetBuf[4];

  vgm_ptr = 0x1c;//ループ位置
  readVgmBytes(offsetBuf, 4);
  uint32_t raw_loop_offset = readLE(offsetBuf,4);
  if (raw_loop_offset == 0) {
    vgm_loop_offset = 0; // ループなし
    } else {
    vgm_loop_offset = 0x1c + raw_loop_offset; // 実際のデータ配列のインデックス
    Serial.printf("Loop offset:%d\n", vgm_loop_offset);
    vgm_loop_count = 0;
  }

  vgm_ptr = 0x34; // 演奏開始位置
  readVgmBytes(offsetBuf, 4);
  uint32_t data_offset = readLE(offsetBuf, 4);
  vgm_ptr = 0x34 + data_offset;  // 演奏開始位置（データストリームの先頭）へシーク
  Serial.println("VGM Playback Started (Timer Interrupt Mode)...");
  isPlaying = true;
  current_block_id = 0; 
  next_vgm_execute_us = esp_timer_get_time(); // micros()の代わりに高精度なesp_timerを使用
}

// VGMファイルのパーサー
void VGM_parser() {
  if (!isPlaying || vgm_data_buffer == NULL) {
    delay(100);
    return;
  }

  // ファイルの終端チェック
  if (vgm_ptr >= vgm_file_size) {
    Serial.println("Reached end of memory buffer.");
    isPlaying = false;
    return;
  }

  // 再生中にボタン4 (BTN4) が押されたら、強制的に再生終了処理へ移行する
  // チャタリングを考慮し、LOW（押されている）かつ少し待ってもLOWなら中断とみなす
  if (getPressedButton() == BTN_4_ID) {
    delayMicroseconds(1000); 
    if (getPressedButton() == BTN_4_ID) {
      Serial.println("[VGM] Interrupted by BTN4.");
      
      // ボタンが離されるまで待つ
      while(getPressedButton() == BTN_4_ID) {
        vTaskDelay(1); 
      }
      
      muteAll();
      portDISABLE_INTERRUPTS();
      adpcm_play_ptr = NULL; adpcm_remaining_bytes = 0;
      portENABLE_INTERRUPTS();      
      isPlaying = false;
      currentMode = MODE_SELECT_FILE;
      drawDisplay();                  
      return;
    }
  }

  uint8_t cmd = readVgmByte(); 
  uint8_t paramBuf[16]; 
  uint32_t w_freq;
  
  switch (cmd) {
    case 0x54://YM2151
      readVgmBytes(paramBuf, 2); 
      writeOPM(paramBuf[0], paramBuf[1]);//YM2151へ書き込み
      break;

    case 0xA0://YM2149,AY8910
      readVgmBytes(paramBuf, 2); 
      writePSG(paramBuf[0], paramBuf[1]);//YM2149へ書き込み
      break;
    
    case 0x61://wait
      readVgmBytes(paramBuf, 2);
      vgmWaitSamples(readLE(paramBuf, 2));
      break;
    
    case 0x62://wait 735 samples
      vgmWaitSamples(735);
      break;

    case 0x63://wait 882 samples
      vgmWaitSamples(882);
      break;

    case 0x66://終端
      vgm_loop_count ++;
      if (vgm_loop_offset > 0 and vgm_loop_count <= vgm_loops) {
        // ループポイントが存在する場合、ポインタをループ先に戻して演奏を続行！
        vgm_ptr = vgm_loop_offset;
        Serial.println("[VGM] Loop triggered!");
        break;
      } else {
        // ループがない曲はそのまま終了
        Serial.println("[VGM] Playback End.");
        muteAll();
        portDISABLE_INTERRUPTS();
        adpcm_play_ptr = NULL; adpcm_remaining_bytes = 0;
        portENABLE_INTERRUPTS();      
        isPlaying = false;
        currentMode = MODE_SELECT_FILE; // ファイル選択モードに戻す
        drawDisplay();                  // ディスプレイを再描画
      }
      break;
      
    case 0x67: {
      readVgmByte(); // 0x66をスキップ
      uint8_t type = readVgmByte(); 
      readVgmBytes(paramBuf, 4);
      uint32_t data_len = readLE(paramBuf, 4);
      vgm_ptr += data_len;
      //PCMは未サポートとする
      break;
    }

    default:
      if ((cmd & 0xF0) == 0x70) {
        vgmWaitSamples((cmd & 0x0F) + 1);
      }
      break;
  }
}

// 指定したディレクトリ内のフォルダ・ファイル一覧を更新する関数
void updateLists() {
  dirList.clear();
  fileList.clear();

  // フォルダ一覧は常にルート直下を検索（仕様に合わせて調整可能）
  File root = SD.open("/");
  if(root){
    // ルート自体を選択肢に含める用
    dirList.push_back("[ ROOT ]");
    while (true) {
      File entry = root.openNextFile();
      if (!entry) break;
      if (entry.isDirectory()) {
        dirList.push_back(String(entry.name()));
      }
      entry.close();
    }
    root.close();
  }

  // 現在選択されたフォルダ内のファイルを検索
  File dir = SD.open(currentDir);
  if(dir){
    while (true) {
      File entry = dir.openNextFile();
      if (!entry) break;
      if (!entry.isDirectory()) {
        fileList.push_back(String(entry.name()));
      }
      entry.close();
    }
    dir.close();
  }
}

// OLED描画処理
void drawDisplay() {
  display.clearDisplay();
  
  // 1行目: フォルダ情報の表示
  display.setCursor(0, 0);
  if (currentMode == MODE_SELECT_DIR) {
    display.print("Dir: ");
    if (!dirList.empty()) display.println(dirList[dirIndex]);
    else display.println("No Dirs");
  } else {
    display.print("Dir: ");
    display.println(currentDir);
  }

  // 2行目: ファイル情報の表示
  display.setCursor(0, 16); // テキストサイズ1の場合、y=16で2行目へ
  if (currentMode == MODE_SELECT_FILE) {
    display.print("VGM: ");
    if (!fileList.empty()) display.println(fileList[fileIndex]);
    else display.println("No Files");
  } else {
    display.println("(Select Dir First)");
  }
  display.display();
}

// 現在押されているボタンのIDを取得する
ButtonID getPressedButton() {
  int val = analogRead(BTN_ADC_PIN);
    if (abs(val - BTN1_ADC_VAL) < ADC_MARGIN) return BTN_1_ID;
  if (abs(val - BTN2_ADC_VAL) < ADC_MARGIN) return BTN_2_ID;
  if (abs(val - BTN3_ADC_VAL) < ADC_MARGIN) return BTN_3_ID;
  if (abs(val - BTN4_ADC_VAL) < ADC_MARGIN) return BTN_4_ID;
    return BTN_NONE; // どのボタンも押されていない
}

// 簡易的なチャタリング防止＆ボタン離脱待ち付きの判定関数
bool checkButton(ButtonID targetBtn) {
  if (getPressedButton() == targetBtn) {
    delay(50); // デバウンス
    if (getPressedButton() == targetBtn) {
      // ボタンが離されるまで待つ（または判定から外れるまで）
      while (getPressedButton() == targetBtn) {
        delay(10);
      }
      return true;
    }
  }
  return false;
}

// PSRAMへの格納処理
void loadFileToPSRAM(String path) {
  // 既にバッファにデータがある場合は解放
  if (vgm_data_buffer != nullptr) {
    free(vgm_data_buffer);
    vgm_data_buffer = nullptr;
    Serial.println("既存のバッファを解放しました。");
  }

  Serial.print("ファイルを読み込み中: ");
  Serial.println(path);

  File vgmFile = SD.open(path, FILE_READ);
  if (!vgmFile) {
    Serial.println("ファイルのオープンに失敗しました。");
    return;
  }

  vgm_file_size = vgmFile.size();
  Serial.print("ファイルサイズ: ");
  Serial.print(vgm_file_size);
  Serial.println(" bytes");

  // ps_malloc を使用してPSRAM上に領域を確保
  vgm_data_buffer = (uint8_t*)ps_malloc(vgm_file_size);

  if (vgm_data_buffer == nullptr) {
    Serial.println("PSRAMのメモリ確保に失敗しました");
    vgmFile.close();
    return;
  }

  // データの読み込み
  size_t readSize = vgmFile.read(vgm_data_buffer, vgm_file_size);
  vgmFile.close();

  Serial.print("PSRAMへの格納が完了しました。読み込みサイズ: ");
  Serial.println(readSize);

  // OLEDに完了画面を一時表示
  display.clearDisplay();
  display.setCursor(0, 0);
  display.println(path);
  display.setCursor(0, 24);
  display.println("Playing...");
  display.display();
  PSRAM_use();
}

void initClocks() {
  // LEDCタイマーの設定 (YM2151のクロック4MHz用)
  ledc_timer_config_t timer_opm = {
    .speed_mode       = LEDC_LOW_SPEED_MODE,
    .duty_resolution  = LEDC_TIMER_1_BIT, // 1-bit（0か1）で50%デューティを作る
    .timer_num        = LEDC_TIMER_0,
    .freq_hz          = 4000000,          // 4MHz
    //.freq_hz          = 3579545,          // 3.58MHz
    .clk_cfg          = LEDC_AUTO_CLK
  };
  ledc_timer_config(&timer_opm);

  ledc_channel_config_t ch_opm = {
    .gpio_num = OPM_CLK, .speed_mode = LEDC_LOW_SPEED_MODE,
    .channel = LEDC_CHANNEL_0, .timer_sel = LEDC_TIMER_0, .duty = 1
  };
  ledc_channel_config(&ch_opm);
  Serial.print("YM2151 Master Clock (");
  Serial.print(timer_opm.freq_hz);
  Serial.println("Hz) initialized on GPIO.");

// YM2149用 (2MHz)
  ledc_timer_config_t timer_psg = {
    .speed_mode       = LEDC_LOW_SPEED_MODE,
    .duty_resolution  = LEDC_TIMER_1_BIT,
    .timer_num        = LEDC_TIMER_1,
    .freq_hz          = 2000000,
    .clk_cfg          = LEDC_AUTO_CLK
  };
  ledc_timer_config(&timer_psg);

  ledc_channel_config_t ch_psg = {
    .gpio_num = PSG_CLK, .speed_mode = LEDC_LOW_SPEED_MODE,
    .channel = LEDC_CHANNEL_1, .timer_sel = LEDC_TIMER_1, .duty = 1
  };
  ledc_channel_config(&ch_psg);
  Serial.print("YM2149 Master Clock (");
  Serial.print(timer_psg.freq_hz);
  Serial.println("Hz) initialized on GPIO.");
}

// YM2151とYM2149の消音
void muteAll() {
  // --- YM2151 (OPM) の消音 ---
  // レジスタ 0x08 (Key On) で全8チャンネル分キーオフ
  for (uint8_t ch = 0; ch < 8; ch++) {
    writeOPM(0x08, ch & 0x07); // Bit 3~6 = 0 (OFF)
  }
  // --- YM2149 (PSG) の消音 ---
  // レジスタ 0x08, 0x09, 0x0A (Ch A, B, C の音量) を 0 に設定
  writePSG(0x07, 0x3F);
  writePSG(0x08, 0x00);
  writePSG(0x09, 0x00);
  writePSG(0x0A, 0x00);
}
