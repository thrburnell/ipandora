import { connect } from 'react-redux'
import FormulaInput from '../components/FormulaInput'
import { addToShow } from '../actions'

const mapStateToProps = () => ({})

const mapDispatchToProps = (dispatch) => (
  {
    onEnterPress: (value) => dispatch(addToShow(value))
  }
)

const RAddToShow = connect(
  mapStateToProps,
  mapDispatchToProps
)(FormulaInput)

export default RAddToShow

