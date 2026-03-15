const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const path = require('path');

const app = express();
const server = http.createServer(app);
const io = new Server(server);

app.use(express.static(path.join(__dirname, 'public')));

// ルーム管理
const rooms = new Map();

function createGameState() {
  return {
    board: { rows: 9, cols: 9 },
    players: [
      { row: 0, col: 4, walls: 10, goal: 8 },  // Player 1: 上から下へ
      { row: 8, col: 4, walls: 10, goal: 0 },  // Player 2: 下から上へ
    ],
    walls: [],        // { row, col, orientation: 'h'|'v' }
    currentPlayer: 0, // 0 or 1
    phase: 'waiting', // waiting, playing, finished
    winner: null,
  };
}

// 壁が既存の壁と重なるかチェック
function wallConflicts(walls, newWall) {
  for (const w of walls) {
    if (w.orientation === newWall.orientation) {
      if (w.orientation === 'h') {
        if (w.row === newWall.row && Math.abs(w.col - newWall.col) < 2) return true;
      } else {
        if (w.col === newWall.col && Math.abs(w.row - newWall.row) < 2) return true;
      }
    } else {
      // 交差チェック
      if (w.row === newWall.row && w.col === newWall.col) return true;
    }
  }
  return false;
}

// 2セル間に壁があるかチェック
function isBlocked(walls, r1, c1, r2, c2) {
  for (const w of walls) {
    if (w.orientation === 'h') {
      // 水平壁: row行とrow+1行の間を塞ぐ（col, col+1の2マス分）
      if (r2 === r1 + 1 && c2 === c1) {
        if (w.row === r1 && (w.col === c1 || w.col === c1 - 1)) return true;
      }
      if (r2 === r1 - 1 && c2 === c1) {
        if (w.row === r2 && (w.col === c1 || w.col === c1 - 1)) return true;
      }
    } else {
      // 垂直壁: col列とcol+1列の間を塞ぐ（row, row+1の2マス分）
      if (c2 === c1 + 1 && r2 === r1) {
        if (w.col === c1 && (w.row === r1 || w.row === r1 - 1)) return true;
      }
      if (c2 === c1 - 1 && r2 === r1) {
        if (w.col === c2 && (w.row === r1 || w.row === r1 - 1)) return true;
      }
    }
  }
  return false;
}

// BFSでゴールへの経路が存在するかチェック
function hasPath(walls, startRow, startCol, goalRow, otherPlayerRow, otherPlayerCol) {
  const visited = new Set();
  const queue = [[startRow, startCol]];
  visited.add(`${startRow},${startCol}`);

  while (queue.length > 0) {
    const [r, c] = queue.shift();
    if (r === goalRow) return true;

    for (const [dr, dc] of [[0, 1], [0, -1], [1, 0], [-1, 0]]) {
      let nr = r + dr;
      let nc = c + dc;
      if (nr < 0 || nr > 8 || nc < 0 || nc > 8) continue;
      if (isBlocked(walls, r, c, nr, nc)) continue;

      // 相手プレイヤーがいる場合は飛び越し
      if (nr === otherPlayerRow && nc === otherPlayerCol) {
        // 直線飛び越し
        const jr = nr + dr;
        const jc = nc + dc;
        if (jr >= 0 && jr <= 8 && jc >= 0 && jc <= 8 && !isBlocked(walls, nr, nc, jr, jc)) {
          if (!visited.has(`${jr},${jc}`)) {
            visited.add(`${jr},${jc}`);
            queue.push([jr, jc]);
          }
        } else {
          // 斜め移動（飛び越せない場合）
          for (const [sr, sc] of [[0, 1], [0, -1], [1, 0], [-1, 0]]) {
            if (sr === -dr && sc === -dc) continue; // 元の方向に戻らない
            const snr = nr + sr;
            const snc = nc + sc;
            if (snr >= 0 && snr <= 8 && snc >= 0 && snc <= 8 && !isBlocked(walls, nr, nc, snr, snc)) {
              if (!visited.has(`${snr},${snc}`)) {
                visited.add(`${snr},${snc}`);
                queue.push([snr, snc]);
              }
            }
          }
        }
        continue;
      }

      if (!visited.has(`${nr},${nc}`)) {
        visited.add(`${nr},${nc}`);
        queue.push([nr, nc]);
      }
    }
  }
  return false;
}

// 移動の妥当性チェック
function isValidMove(state, playerIdx, toRow, toCol) {
  const player = state.players[playerIdx];
  const other = state.players[1 - playerIdx];
  const fr = player.row, fc = player.col;
  const dr = toRow - fr, dc = toCol - fc;

  if (toRow < 0 || toRow > 8 || toCol < 0 || toCol > 8) return false;
  if (toRow === other.row && toCol === other.col) return false;

  // 隣接移動
  if ((Math.abs(dr) === 1 && dc === 0) || (dr === 0 && Math.abs(dc) === 1)) {
    return !isBlocked(state.walls, fr, fc, toRow, toCol);
  }

  // 飛び越し移動（相手を飛び越す）
  if (Math.abs(dr) === 2 && dc === 0) {
    const midR = fr + dr / 2;
    if (midR === other.row && fc === other.col) {
      return !isBlocked(state.walls, fr, fc, midR, fc) && !isBlocked(state.walls, midR, fc, toRow, toCol);
    }
  }
  if (dr === 0 && Math.abs(dc) === 2) {
    const midC = fc + dc / 2;
    if (fr === other.row && midC === other.col) {
      return !isBlocked(state.walls, fr, fc, fr, midC) && !isBlocked(state.walls, fr, midC, toRow, toCol);
    }
  }

  // 斜め移動（飛び越しが壁で塞がれている場合）
  if (Math.abs(dr) === 1 && Math.abs(dc) === 1) {
    // 縦方向に相手がいて、その先が壁
    if (fr + dr === fr && fc === other.col) return false; // not applicable
    // パターン1: 縦に相手→その先壁→横に移動
    if (other.row === fr + dr && other.col === fc) {
      if (!isBlocked(state.walls, fr, fc, other.row, other.col)) {
        const beyondR = other.row + dr;
        if (beyondR < 0 || beyondR > 8 || isBlocked(state.walls, other.row, other.col, beyondR, other.col)) {
          return !isBlocked(state.walls, other.row, other.col, other.row, other.col + dc);
        }
      }
    }
    // パターン2: 横に相手→その先壁→縦に移動
    if (other.row === fr && other.col === fc + dc) {
      if (!isBlocked(state.walls, fr, fc, other.row, other.col)) {
        const beyondC = other.col + dc;
        if (beyondC < 0 || beyondC > 8 || isBlocked(state.walls, other.row, other.col, other.row, beyondC)) {
          return !isBlocked(state.walls, other.row, other.col, other.row + dr, other.col);
        }
      }
    }
  }

  return false;
}

// 壁配置の妥当性チェック
function isValidWall(state, playerIdx, wall) {
  const player = state.players[playerIdx];
  if (player.walls <= 0) return false;
  if (wall.row < 0 || wall.row > 7 || wall.col < 0 || wall.col > 7) return false;
  if (wallConflicts(state.walls, wall)) return false;

  // 仮配置して経路チェック
  const testWalls = [...state.walls, wall];
  const p0 = state.players[0];
  const p1 = state.players[1];
  if (!hasPath(testWalls, p0.row, p0.col, p0.goal, p1.row, p1.col)) return false;
  if (!hasPath(testWalls, p1.row, p1.col, p1.goal, p0.row, p0.col)) return false;

  return true;
}

function generateRoomId() {
  const chars = 'abcdefghijklmnopqrstuvwxyz0123456789';
  let id = '';
  for (let i = 0; i < 6; i++) id += chars[Math.floor(Math.random() * chars.length)];
  return id;
}

io.on('connection', (socket) => {
  console.log('接続:', socket.id);

  socket.on('createRoom', (callback) => {
    const roomId = generateRoomId();
    const state = createGameState();
    rooms.set(roomId, { state, players: [socket.id] });
    socket.join(roomId);
    socket.roomId = roomId;
    socket.playerIdx = 0;
    callback({ roomId, playerIdx: 0 });
  });

  socket.on('joinRoom', (roomId, callback) => {
    const room = rooms.get(roomId);
    if (!room) return callback({ error: 'ルームが見つかりません' });
    if (room.players.length >= 2) return callback({ error: 'ルームが満員です' });

    room.players.push(socket.id);
    socket.join(roomId);
    socket.roomId = roomId;
    socket.playerIdx = 1;
    room.state.phase = 'playing';

    callback({ roomId, playerIdx: 1 });
    io.to(roomId).emit('gameStart', room.state);
  });

  socket.on('move', ({ toRow, toCol }) => {
    const room = rooms.get(socket.roomId);
    if (!room || room.state.phase !== 'playing') return;
    if (room.state.currentPlayer !== socket.playerIdx) return;

    if (!isValidMove(room.state, socket.playerIdx, toRow, toCol)) {
      return socket.emit('invalidAction', '移動できません');
    }

    room.state.players[socket.playerIdx].row = toRow;
    room.state.players[socket.playerIdx].col = toCol;

    // 勝利判定
    if (toRow === room.state.players[socket.playerIdx].goal) {
      room.state.phase = 'finished';
      room.state.winner = socket.playerIdx;
      io.to(socket.roomId).emit('gameUpdate', room.state);
      return;
    }

    room.state.currentPlayer = 1 - room.state.currentPlayer;
    io.to(socket.roomId).emit('gameUpdate', room.state);
  });

  socket.on('placeWall', ({ row, col, orientation }) => {
    const room = rooms.get(socket.roomId);
    if (!room || room.state.phase !== 'playing') return;
    if (room.state.currentPlayer !== socket.playerIdx) return;

    const wall = { row, col, orientation };
    if (!isValidWall(room.state, socket.playerIdx, wall)) {
      return socket.emit('invalidAction', '壁を置けません');
    }

    room.state.walls.push(wall);
    room.state.players[socket.playerIdx].walls--;
    room.state.currentPlayer = 1 - room.state.currentPlayer;
    io.to(socket.roomId).emit('gameUpdate', room.state);
  });

  socket.on('rematch', () => {
    const room = rooms.get(socket.roomId);
    if (!room) return;
    if (!room.rematchVotes) room.rematchVotes = new Set();
    room.rematchVotes.add(socket.playerIdx);
    if (room.rematchVotes.size >= 2) {
      room.state = createGameState();
      room.state.phase = 'playing';
      room.rematchVotes = new Set();
      io.to(socket.roomId).emit('gameStart', room.state);
    } else {
      socket.emit('rematchWaiting');
    }
  });

  socket.on('disconnect', () => {
    const room = rooms.get(socket.roomId);
    if (room) {
      room.players = room.players.filter(id => id !== socket.id);
      if (room.players.length === 0) {
        rooms.delete(socket.roomId);
      } else {
        io.to(socket.roomId).emit('opponentLeft');
      }
    }
  });
});

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
  console.log(`コリドール サーバー起動: http://localhost:${PORT}`);
});
