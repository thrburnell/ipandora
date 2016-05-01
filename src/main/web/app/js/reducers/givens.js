const givens = (state = [], action) => {
  switch (action.type) {
    case 'ADD_GIVEN':
      return [
        ...state,
        {
          id: action.id,
          formula: action.formula
        }
      ]
    default:
      return state
  }
}

export default givens

