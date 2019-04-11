bms.observe('formula', {
  selector: "#board",
  translate: true,
  formulas: ["white", "black"],
  trigger: function(origin, res) {
    origin.find(".image").attr("xlink:href", "ChessPieces/empty.png");
    origin.find(".image").attr("class", "image");

    res.forEach(function(result) {
      result.forEach(function(r) {
        var x = r[0][0];
        var y = r[0][1];
        var val = r[1];
        var element = origin.find("#" + x + "_" + y);
        element.attr("xlink:href", "ChessPieces/" + val + ".png");
        element.attr("class", "image " + val);
      });
    });
  }
});

var moving;

bms.observe('formula', {
  translate: true,
  formulas: ["moving"],
  trigger: function(res) {
    moving = res[0];
    if (moving === false) {
      bms.callMethod({
        name: "alphaBeta",
        args: [],
        callback: function(data) {
          console.log("Found value = " + data);
        }
      });
    }
  }
});

var currentX = 0, currentY = 0, currentFigure = null, color = null;
var take = null;
var newFigure = null;

function click(evt) {
  var element = evt.target;
  var vals = element.id.split("_");
  var x = vals[0];
  var y = vals[1];
  var figure = element.getAttribute("class").split(" ")[1];

  // either a field is already marked (and the operation is call) or it will be marked
  if (currentX === 0 && currentY === 0 && currentFigure === null && color === null) {
    currentX = x;
    currentY = y;
    currentFigure = figure;
    var field = evt.path[1].getElementsByClassName("rect")[x+"-"+y];
    color = field.getAttribute("fill");
    field.setAttribute("fill", "green");

    // check for promotion and enable buttons if so
    if ((y == 7 && figure == "w_pawn") || (y == 2 && figure == "b_pawn")) {
      enableButtons(evt);
    }
  } else {
    // check if second field is different
    if (!(currentX == x && currentY == y)) {
      if (figure) {
        execute(x, y, 1);
      } else {
        execute(x, y, 0);
      }
    }

    // reset color
    evt.path[1].getElementsByClassName("rect")[currentX+"-"+currentY].setAttribute("fill", color);

    // reset variables
    currentX = 0;
    currentY = 0;
    currentFigure = null;
    color = null;
  }
}

function enableButtons(evt) {
  var elements = evt.path[1].getElementsByClassName("promotion");
  for (var i = 0 ; i < elements.length; i++) {
    elements[i].setAttribute("style", "");
  }

  var texts = evt.path[1].getElementsByClassName("text");
  for (var j = 0; j < texts.length; j++) {
    texts[j].setAttribute("fill", "black");
  }
}

function setFigure(evt) {
  newFigure = evt.target.id;

  var elements = evt.path[1].getElementsByClassName("promotion");
  for (var i = 0 ; i < elements.length; i++) {
    elements[i].setAttribute("style", "visibility: hidden");
  }

  var texts = evt.path[1].getElementsByClassName("text");
  for (var j = 0; j < texts.length; j++) {
    texts[j].setAttribute("fill", "white");
  }
}

function execute(x, y, take) {
  if (moving) {
    bms.executeEvent({
      name: "move_white",
      predicate: function() {
        return "figure=" + currentFigure +
          " & a=" + currentX + " & b=" + currentY +
          " & x=" + x + " & y=" + y + "& take=" + take;
      }
    });
    bms.executeEvent({
      name: "white_castling"
    });
    bms.executeEvent({
      name: "white_en_passant"
    });
    bms.executeEvent({
      name: "white_promotion",
      predicate: function() {
        if (newFigure !== null) {
          return "x=" + x + " & new_figure=w_" + newFigure;
        }
        return "x=" + x + " & new_figure=w_queen";
      }
    });
  } else {
    bms.executeEvent({
      name: "move_black",
      predicate: function() {
        return "figure=" + currentFigure +
          " & a=" + currentX + " & b=" + currentY +
          " & x=" + x + " & y=" + y + "& take=" + take;
      }
    });
    bms.executeEvent({
      name: "black_castling"
    });
    bms.executeEvent({
      name: "black_en_passant"
    });
    bms.executeEvent({
      name: "black_promotion",
      predicate: function() {
        if (newFigure !== null) {
          return "x=" + x + " & new_figure=b_" + newFigure;
        }
        return "x=" + x + " & new_figure=b_queen";
      }
    });
  }
}
