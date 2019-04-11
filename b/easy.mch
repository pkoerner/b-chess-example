/*
  Title: A formal-based chess engine for ProB
  Author: Phillip Höfges
  Heinrich-Heine-Universität Düsseldorf
  Lehrstuhl für Softwaretechnik und Programmiersprachen
  Prof. Dr. Michael Leuschel, Sebastian Krings
*/

MACHINE easy
VARIABLES value
INVARIANT value : INT
INITIALISATION value := 0
OPERATIONS
  level1Left =
    PRE value = 0
    THEN
      value := -10
    END;
  level1Right =
    PRE value = 0
    THEN
      value := 10
    END;
  level2LeftLeft =
    PRE value = -10
    THEN
      value := 2
    END;
  level2LeftRight =
    PRE value = -10
    THEN
      value := 7
    END;
  level2RightLeft =
    PRE value = 10
    THEN
      value := 1
    END;
  level2RightRight =
    PRE value = 10
    THEN
      value := 8
    END
END
