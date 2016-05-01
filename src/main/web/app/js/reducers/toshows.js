const toShows = (state = [], action) => {
  switch (action.type) {
    case 'ADD_TO_SHOW':
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

export default toShows

