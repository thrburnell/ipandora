let nextGivenId = 1

export const addGiven = (formula) => {
  return {
    type: 'ADD_GIVEN',
    id: nextGivenId++,
    formula
  }
}

let nextToShowId = 945 // small alpha

export const addToShow = (formula) => {
  return {
    type: 'ADD_TO_SHOW',
    id: String.fromCharCode(nextToShowId++),
    formula
  }
}

