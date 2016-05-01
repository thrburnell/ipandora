let nextGivenId = 1

export const addGiven = (formula) => {
  return {
    type: 'ADD_GIVEN',
    id: nextGivenId++,
    formula
  }
}

let nextToShowId = 1;

export const addToShow = (formula) => {
  return {
    type: 'ADD_TO_SHOW',
    id: nextToShowId++,
    formula
  }
}

